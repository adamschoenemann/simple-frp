{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE AutoDeriveTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
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


class FRPHask (t :: Ty) (a :: *) | t -> a where
  toHask :: Sing t -> Value -> a
  toFRP :: a -> (Sing t, Value)

instance FRPHask TNat Int where
  toHask sing (VLit (LInt x)) = x
  toHask _ _ = error "expected nat value"
  toFRP x = (SNat, VLit . LInt $ x)

instance FRPHask TBool Bool where
  toHask sing (VLit (LBool x)) = x
  toHask _ _ = error "expected bool value"
  toFRP x = (SBool, VLit . LBool $ x)

instance (FRPHask t1 a, FRPHask t2 b) => FRPHask (t1 :*: t2) (a,b) where
  toHask (SProd t1 t2) (VTup x y) = (toHask t1 x, toHask t2 y)
  toHask _ _ = error "expected tuple value"
  toFRP (x,y) =
    let (s1, t1) = toFRP x
        (s2, t2) = toFRP y
    in (SProd s1 s2, VTup t1 t2)

instance (FRPHask t1 a, FRPHask t2 b) => FRPHask (t1 :+: t2) (Either a b) where
  toHask (SSum t1 t2) (VInl x) = Left (toHask t1 x)
  toHask (SSum t1 t2) (VInr x) = Right (toHask t2 x)
  toHask _ _ = error "expected tuple value"
  toFRP (Left x) =
    let (s, t) = toFRP x
    in  (SSum s undefined, VInl t)
  toFRP (Right x) =
    let (s, t) = toFRP x
    in  (SSum undefined s, VInr t)


transform :: (FRPHask t1 a, FRPHask t2 b)
          => FRP (TStream TAlloc :->: TStream t1 :->: TStream t2)
          -> [a] -> [b]
transform (FRP trm (SArr us (SArr t1s t2s))) as =
  case as of
    [] -> []
    (x : xs) -> [toHask t2s $ evalExpr initEnv (mkExpr x)]
  where
    mkExpr x = (trm <| fixed tmalloc <| fixed (valToTerm . snd . toFRP $ x))
    fixed e = tmfix "_xs" undefined
              $ tmcons e (tmdelay tmalloc "_xs")
