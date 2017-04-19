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

module FRP.AST.Reflect where

import Language.Haskell.TH ( runQ, Q, Exp(..), Pat(..), mkName, Lit(..)
                           , ExpQ
                           )

import FRP.AST
import qualified Language.Haskell.TH as T

import           Data.Data

data Ty
  = TNat
  | TBool
  | TAlloc
  | Ty :*: Ty
  | Ty :+: Ty
  | Ty :->: Ty
  | TStream Ty
  deriving (Show, Eq, Typeable, Data)


infixr 0 :->:
infixr 6 :*:
infixr 5 :+:

data Sing :: Ty -> * where
  SNat    :: Sing TNat
  SBool   :: Sing TBool
  SAlloc  :: Sing TAlloc
  SProd   :: Sing t1 -> Sing t2 -> Sing (t1 :*: t2)
  SSum    :: Sing t1 -> Sing t2 -> Sing (t1 :+: t2)
  SArr    :: Sing t1 -> Sing t2 -> Sing (t1 :->: t2)
  SStream :: Sing t  -> Sing (TStream t)

deriving instance Eq (Sing a)
deriving instance Show (Sing a)
deriving instance Typeable (Sing a)

data FRP :: Ty -> * where
  FRP :: Term () -> Sing t -> FRP t

deriving instance Typeable (FRP t)
deriving instance Show (FRP t)


typeToSingExp :: Type a -> ExpQ
typeToSingExp typ = case typ of
  TyPrim _ TyNat  -> runQ [| SNat |]
  TyPrim _ TyBool -> runQ [| SBool |]
  TyAlloc _       -> runQ [| SAlloc |]
  TySum _ t1 t2 ->
    let e1 = typeToSingExp t1
        e2 = typeToSingExp t2
    in  runQ [| SSum $(e1) $(e2) |]
  TyProd _ t1 t2    ->
    let e1 = typeToSingExp t1
        e2 = typeToSingExp t2
    in  runQ [| SProd $(e1) $(e2) |]
  TyArr _ t1 t2    ->
    let e1 = typeToSingExp t1
        e2 = typeToSingExp t2
    in  runQ [| SArr $(e1) $(e2) |]
  TyStream _ t ->
    let e = typeToSingExp t
    in  runQ [| SStream $(e) |]
  TyStable _ t -> typeToSingExp t
  TyLater  _ t -> typeToSingExp t


