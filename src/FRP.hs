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
  , transform
  , execute
  , FRPHask
  )
  where

import           FRP.AST
import           FRP.AST.Construct
import           FRP.AST.Reflect
import           FRP.Semantics



haskErr :: String -> Sing t -> Value -> a
haskErr msg sing v =
  error $ msg ++ " but got (" ++ show sing ++ ") (" ++ show v ++ ")"

class FRPHask (t :: Ty) (a :: *) | t -> a where
  toHask :: Sing t -> Value -> a
  toFRP :: Sing t -> a -> Value

instance FRPHask TNat Int where
  toHask sing (VLit (LInt x)) = x
  toHask sing v               = haskErr "expected nat value" sing v

  toFRP _ x = VLit . LInt $ x

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


-- lazy evaluation allows us to do this, where we construct the possibly infinite
-- term of conses from the input list that is not fully evaluated until
-- the ith iteration
transform :: (FRPHask t1 a, FRPHask t2 b)
          => FRP (TStream TAlloc :->: TStream t1 :->: TStream t2)
          -> [a] -> [b]
transform frp@(FRP env trm sing@(SArr us (SArr (SStream s1) (SStream s2)))) as =
  map (toHask s2) $ toHaskList $ runTermInEnv env $ mkExpr trm s1 as
  where
    -- unused right now
    help st tm = \case
      [] -> []
      (x : xs) ->
          let r@((VCons v (VPntr l)), st1) = runExpr st initEnv tm
          in  toHask s2 v : help (tick st1) (tmpntrderef l) xs
    mkExpr :: (FRPHask t a) => Term () -> Sing t -> [a] -> Term ()
    mkExpr tm s xs = tm <| fixed tmalloc <| streamed s xs

    streamed s [] = error "input stream terminated"
    streamed s (x : xs) = tmcons (valToTerm . toFRP s $ x) (tmdelay tmalloc $ streamed s xs)
    uncons ((VCons x l), s') = x


execute :: (FRPHask t a) => FRP (TStream TAlloc :->: TStream t) -> [a]
execute frp@(FRP env trm sing@(SArr us (SStream s))) =
  map (toHask s) $ toHaskList $ runTermInEnv env $ mkExpr trm
  where
    mkExpr tm = tm <| fixed tmalloc


fixed :: Term () -> Term ()
fixed e = tmfix "_xs" (tystream $ tyalloc)
          $ tmcons e (tmdelay tmalloc "_xs")
