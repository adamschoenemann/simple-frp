{-|
Module      : FRP.AST.Reflect
Description : Reflecting FRP-Types into the Haskell type-system

-}
{-# LANGUAGE AutoDeriveTypeable  #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeOperators       #-}

module FRP.AST.Reflect where

import           Language.Haskell.TH ( Exp (..), ExpQ, Lit (..), Pat (..), Q
                                     , mkName, runQ)

import           FRP.AST
import           FRP.AST.Construct
import qualified Language.Haskell.TH as T

import           Data.Data

-- -----------------------------------------------------------------------------
-- Ty
-- -----------------------------------------------------------------------------

-- | The type of FRP-types that can be reflected
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

-- -----------------------------------------------------------------------------
-- Sing
-- -----------------------------------------------------------------------------

-- |Singleton representation to lift Ty into types
-- using kind-promotion
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

-- |Reify a singleton back into an FRP type
reify :: Sing t -> Type ()
reify = \case
  SNat    -> tynat
  SBool   -> tybool
  SAlloc  -> tyalloc

  SProd   t1 t2 -> reify t1 .*. reify t2
  SSum    t1 t2 -> reify t1 .+. reify t2
  SArr    t1 t2 -> reify t1 |-> reify t2
  SStream t -> reify t

-- -----------------------------------------------------------------------------
-- FRP
-- -----------------------------------------------------------------------------

-- |An FRP program of a type, executed in an environment
data FRP :: Ty -> * where
  FRP :: Env -> Term () -> Sing t -> FRP t

deriving instance Typeable (FRP t)
deriving instance Show (FRP t)

-- |Use template haskell to generate a singleton value that represents
-- an FRP type
typeToSingExp :: Type a -> ExpQ
typeToSingExp typ = case typ of
  TyPrim _ TyNat  -> T.conE 'SNat
  TyPrim _ TyBool -> T.conE 'SBool
  TyAlloc _       -> T.conE 'SAlloc
  TySum _ t1 t2 ->
    let e1 = typeToSingExp t1
        e2 = typeToSingExp t2
    in  T.conE 'SSum `T.appE` e1 `T.appE` e2
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
  TyVar _ _    -> fail "FRP types must be fully instantiated when marshalled"
  TyRec _ _ _  -> fail "Recursive types are not supported"


