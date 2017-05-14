{-|
Module      : FRP
Description : Entry-point for the library

Exports functions to execute FRP programs, and use them as
stream transformers
-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}

module FRP
  ( module FRP.AST
  , module FRP.Semantics
  , module FRP.AST.QuasiQuoter
  , transform
  , execute
  , FRPHask
  )
  where

import FRP.AST
import FRP.AST.Construct
import FRP.AST.Reflect
import FRP.AST.QuasiQuoter
import FRP.Pretty (ppshow)
import FRP.Semantics
import Debug.Trace
import qualified Data.Map.Strict as M

-- |Type-class that represents a conversion from a FRP value of
-- a type to a Haskell value of a type
class FRPHask (t :: Ty) (a :: *) | a -> t where
  toHask :: Sing t -> Value -> a
  toFRP :: Sing t -> a -> Value

-- |An error when converting a FRP value to a Haskell value
haskErr :: String -> Sing t -> Value -> a
haskErr msg sing v =
  error $ msg ++ " but got (" ++ show sing ++ ") (" ++ show v ++ ")"


instance FRPHask TNat Int where
  toHask sing (VLit (LNat x)) = x
  toHask sing v               = haskErr "expected nat value" sing v

  toFRP _ x = VLit . LNat $ x

instance FRPHask TNat Integer where
  toHask sing (VLit (LNat x)) = toInteger x
  toHask sing v               = haskErr "expected nat value" sing v

  toFRP _ x = VLit . LNat $ fromInteger x

instance FRPHask TBool Bool where
  toHask sing (VLit (LBool x)) = x
  toHask sing v                = haskErr "expected bool value" sing v

  toFRP s x = VLit . LBool $ x

instance (FRPHask t1 a, FRPHask t2 b) => FRPHask (t1 :*: t2) (a,b) where
  toHask (SProd t1 t2) (VTup x y) = (toHask t1 x, toHask t2 y)
  toHask sing v                   = haskErr "expected tuple value" sing v

  toFRP (SProd s1 s2) (x,y) =
    let t1 = toFRP s1 x
        t2 = toFRP s2 y
    in VTup t1 t2

instance (FRPHask t1 a, FRPHask t2 b) => FRPHask (t1 :+: t2) (Either a b) where
  toHask (SSum t1 t2) (VInl x) = Left (toHask t1 x)
  toHask (SSum t1 t2) (VInr x) = Right (toHask t2 x)
  toHask sing v                = haskErr "expected tuple value" sing v

  toFRP (SSum s1 _) (Left x) =
    let v = toFRP s1 x
    in  VInl v
  toFRP (SSum _ s1) (Right x) =
    let v = toFRP s1 x
    in  VInr v

instance FRPHask t1 a => FRPHask (TStream t1) [a] where
  toHask sing@(SStream s) (VCons x l) = toHask s x : toHask sing l
  toHask sing v                       = haskErr "expected stream value" sing v

  toFRP (SStream s) (x : xs) = VCons (toFRP s x) (toFRP (SStream s) xs)
  toFRP sing        []       = error "Cannot convert inductive lists to FRP"



-- |Use a FRP program to transform a Haskell stream @[a]@ to @[b]@
transform :: (FRPHask t1 a, FRPHask t2 b)
          => FRP (TStream TAlloc :->: TStream t1 :->: TStream t2)
          -> [a] -> [b]
transform frp [] = []
transform (FRP env trm (us `SArr` SStream s1 `SArr` SStream s2)) as =
  run initialState (mkExpr trm) as
  where
    run sig e []       = []
    run sig e (x : xs) = step (runExpr (tick inputs sig) inputs env e)
      where
        inputs = mkInputs x
        step (VCons y (VPntr l), sig') = toHask s2 y : run sig' (tmpntrderef l) xs
        step v                         = crash v

    mkInputs x = Inputs (M.singleton "input" (toFRP s1 x))
    crash v    = error $ "got " ++ ppshow v ++ " expected VCons x (VPntr l)"
    mkExpr tm  = tm <| fixed tmalloc <| TmInput () "input"

-- |Execute a FRP program that produces a stream of @[a]@s
execute :: (FRPHask t a) => FRP (TStream TAlloc :->: TStream t) -> [a]
execute (FRP env trm (us `SArr` SStream s)) =
  map (toHask s) $ toHaskList $ runTermInEnv env $ mkExpr trm
  where
    mkExpr tm = tm <| fixed tmalloc

-- |Take a term and put it in an infinite fixpoint
fixed :: Term () -> Term ()
fixed e = tmfix "_xs" (tystream $ tyalloc)
          $ tmcons e (tmdelay tmalloc "_xs")

