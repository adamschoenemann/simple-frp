{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}

module FRP
  ( module FRP.AST
  , module FRP.Semantics
  , module FRP
  )
  where

import FRP.AST
import FRP.AST.Construct
import FRP.AST.Reflect
import FRP.Semantics


haskErr :: String -> Sing t -> Value -> a
haskErr msg sing v =
  error $ msg ++ " but got (" ++ show sing ++ ") (" ++ show v ++ ")"

class FRPHask (t :: Ty) (a :: *) | t -> a where
  toHask :: Sing t -> Value -> a
  toFRP :: Sing t -> a -> Value

instance FRPHask TNat Int where
  toHask sing (VLit (LInt x)) = x
  toHask sing v = haskErr "expected nat value" sing v

  toFRP _ x = VLit . LInt $ x

instance FRPHask TBool Bool where
  toHask sing (VLit (LBool x)) = x
  toHask sing v = haskErr "expected bool value" sing v

  toFRP s x = VLit . LBool $ x

instance (FRPHask t1 a, FRPHask t2 b) => FRPHask (t1 :*: t2) (a,b) where
  toHask (SProd t1 t2) (VTup x y) = (toHask t1 x, toHask t2 y)
  toHask sing v = haskErr "expected tuple value" sing v

  toFRP (SProd s1 s2) (x,y) =
    let t1 = toFRP s1 x
        t2 = toFRP s2 y
    in VTup t1 t2

instance (FRPHask t1 a, FRPHask t2 b) => FRPHask (t1 :+: t2) (Either a b) where
  toHask (SSum t1 t2) (VInl x) = Left (toHask t1 x)
  toHask (SSum t1 t2) (VInr x) = Right (toHask t2 x)
  toHask sing v = haskErr "expected tuple value" sing v

  toFRP (SSum s1 _) (Left x) =
    let v = toFRP s1 x
    in  VInl v
  toFRP (SSum _ s1) (Right x) =
    let v = toFRP s1 x
    in  VInr v

instance FRPHask t1 a => FRPHask (TStream t1) [a] where
  toHask (SStream s) (VCons x l) = [toHask s x]
  toHask sing v = haskErr "expected stream value" sing v

  toFRP (SStream s) (x : xs) = VCons (toFRP s x) (toFRP (SStream s) xs)


transform :: (FRPHask t1 a, FRPHask t2 b)
          => FRP (TStream TAlloc :->: TStream t1 :->: TStream t2)
          -> [a] -> [b]
transform frp@(FRP trm (SArr us (SArr (SStream s1) (SStream s2)))) as =
  case as of
    [] -> []
    (x : xs) -> (toHask s2 $ uncons $ evalExpr initEnv (mkExpr s1 x))
                  : transform frp xs
  where
    mkExpr :: (FRPHask t a) => Sing t -> a -> Term ()
    mkExpr s x =
        let v = toFRP s x
        in  trm <| fixed tmalloc <| fixed (valToTerm v)

    uncons (VCons x _) = x

    fixed :: Term () -> Term ()
    fixed e = tmfix "_xs" undefined
              $ tmcons e (tmdelay tmalloc "_xs")
