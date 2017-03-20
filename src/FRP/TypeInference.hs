
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}

module FRP.TypeInference where

import           Control.Monad.Except
import           Control.Monad.State
import           FRP.Pretty
import           Data.Map.Strict                (Map)
import qualified Data.Map.Strict                as M
import           Data.Set                       (Set)
import qualified Data.Set                       as S
import           FRP.AST
import           FRP.AST.Construct (tmvar)
import           Debug.Trace
import           Data.Maybe (isJust)


data Scheme a = Forall [TVar] (Type a)
  deriving (Show, Eq)

instance Pretty (Scheme a) where
  ppr n (Forall vs tau) =
    text "forall" <+> hcat (map text vs) <> char '.' <+> ppr 0 tau


type QualTy t = (Scheme t, Qualifier)

newtype Context t = Ctx {unCtx :: Map Name (QualTy t)} deriving (Show, Eq)

emptyCtx :: Context t
emptyCtx = Ctx M.empty

instance Pretty (Context t) where
  ppr n (Ctx map) = vcat $ fmap mapper $ M.toList map where
    mapper (k, v) = text k <+> char ':' <+> ppr 0 v

newtype TyExcept t = TyExcept (TyErr t, Context t)
  deriving (Show, Eq)

data TyErr t
  = CannotUnify (QualTy t) (QualTy t) (Term t)
  | OccursCheckFailed Name (Type t)
  | UnknownIdentifier Name
  | NotSyntax (Term t)
  | TypeAnnRequired (Term t)
  | NotStableTy (QualTy t)
  | NotStableVar Name
  | NotNow (Term t)
  deriving (Show, Eq)

instance Pretty (TyExcept t) where
  ppr n (TyExcept (err, ctx)) = ppr n err $$ text "in context: " $$ ppr n ctx

instance Pretty (TyErr t) where
  ppr n = \case
    CannotUnify t1 t2 trm ->
      text "Cannot unify expected type"
            <+> ppr 0 t1
            <+> text "with"
            <+> ppr 0 t2
            <+> text "at" <+> ppr 0 trm

    OccursCheckFailed nm ty -> text nm <+> "occurs in" <+> (ppr 0 ty)
    UnknownIdentifier nm    -> text "unkown identifier" <+> text nm
    NotSyntax trm           -> ppr 0 trm <+> "is not syntax"
    TypeAnnRequired trm     -> ppr 0 trm <+> text "requires a type annotation"
    NotStableTy ty          -> text "expected" <+> ppr n ty  <+> text "to be a stable type"
    NotStableVar v          -> text "expected" <+> text v <+> text "to be stable"
    NotNow    trm           -> text "expected" <+> ppr n trm <+> text "to be now"

typeErr :: TyErr t -> Context t -> Infer t a
typeErr err ctx = throwError (TyExcept (err, ctx))


newtype Infer t a = Infer (ExceptT (TyExcept t) (State [Name]) a)
  deriving ( Functor, Applicative, Monad, MonadState [Name]
           , MonadError (TyExcept t))

freshName :: Infer t Name
freshName = do
  nm:nms <- get
  put nms
  return nm

-- runInferTerm ctx t = runInfer (checkTerm ctx t)
-- runInferTerm' t = runInfer (checkTerm emptyCtx t)

runInfer :: Infer t a -> Either (TyExcept t) a
runInfer (Infer m) = evalState (runExceptT m) (infiniteSupply alphabet)
  where
    alphabet = map (:[]) ['a'..'z']
    infiniteSupply supply = supply ++ addSuffixes supply (1 :: Integer)
    addSuffixes xs n = (map (\x -> addSuffix x n) xs) ++ (addSuffixes xs (n+1))
    addSuffix x n = x ++ show n


type TVar = Name
type Subst a = Map TVar (Type a)

nullSubst :: Subst a
nullSubst = M.empty

class Substitutable a b | a -> b where
  apply :: Subst b -> a -> a
  ftv   :: a -> Set TVar

compose :: Subst a -> Subst a -> Subst a
s1 `compose` s2 = M.map (apply s1) s2 `M.union` s1

(+++) = S.union

instance Substitutable (Type a) a where
  apply st typ = case typ of
    TyVar    a name   -> M.findWithDefault typ name st
    TyProd   a l r    -> TyProd a (apply st l) (apply st r)
    TySum    a l r    -> TySum a (apply st l) (apply st r)
    TyArr    a t1 t2  -> TyArr a (apply st t1) (apply st t2)
    TyLater  a ty     -> TyLater a (apply st ty)
    TyStable a ty     -> TyStable a (apply st ty)
    TyStream a ty     -> TyStream a (apply st ty)
    TyAlloc  a        -> TyAlloc a
    TyPrim{}          -> typ

  ftv = \case
    TyVar    _ name   -> S.singleton name
    TyProd   _ l r    -> ftv l +++ ftv r
    TySum    _ l r    -> ftv l +++ ftv r
    TyArr    _ t1 t2  -> ftv t1 +++ ftv t2
    TyLater  _ ty     -> ftv ty
    TyStable _ ty     -> ftv ty
    TyStream _ ty     -> ftv ty
    TyAlloc  _        -> S.empty
    TyPrim{}          -> S.empty

instance Substitutable (Scheme a) a where
  apply st (Forall vs t) =
    let st' = foldr M.delete st vs
    in  Forall vs $ apply st' t

  ftv (Forall vs t) = ftv t `S.difference` S.fromList vs

instance Substitutable a a => Substitutable [a] a  where
  apply = fmap . apply
  ftv   = foldr ((+++) . ftv) S.empty

-- not sure this is useful for us
-- since the type parameters are getting in our way
instance Substitutable (QualTy a) a where
  apply st (ty, q) = (apply st ty, q)
  ftv (ty, q)      = ftv ty

instance Substitutable (Context a) a where
  apply s (Ctx ctx) = Ctx $ M.map (apply s) ctx
  ftv (Ctx ctx)     = foldr ((+++) . ftv) S.empty $ M.elems ctx

occursCheck :: Substitutable a b => TVar -> a -> Bool
occursCheck a t = a `S.member` ftv t


bind :: TVar -> Type a -> Infer a (Subst a)
bind a t | unitFunc t == TyVar () a = return nullSubst
         | occursCheck a t = typeErr (OccursCheckFailed a t) emptyCtx
         | otherwise       = return $ M.singleton a t

unify :: Type a -> Type a -> Infer a (Subst a)
unify type1 type2 = case (type1, type2) of

  (TyArr _ l1 r1, TyArr _ l2 r2) -> do
    s1 <- unify l1 l2
    s2 <- unify (apply s1 r1) (apply s1 r2)
    return (s2 `compose` s1)

  (TyVar _ a, t) -> bind a t

  (t, TyVar _ a) -> bind a t

  (TyPrim _ p1, TyPrim _ p2) | p1 == p2 -> return nullSubst

  (TyProd _a ll lr, TyProd _b rl rr) -> do
    s1 <- unify ll rl
    s2 <- unify rl rr
    return (s2 `compose` s1)

  (TySum  _a ll lr, TySum  _b rl rr) -> do
    s1 <- unify ll rl
    s2 <- unify rl rr
    return (s2 `compose` s1)

  (TyLater  _ lt, TyLater  _ rt) -> unify lt rt
  (TyStable _ lt, TyStable _ rt) -> unify lt rt
  (TyStream _ lt, TyStream _ rt) -> unify lt rt

  (TyAlloc{}, TyAlloc{}) -> return nullSubst

  (ty1, ty2) ->
    let noterm = error "no term in function unify"
        sig = Forall []
    in  typeErr (CannotUnify (sig ty1, QNow) (sig ty2, QNow) noterm) emptyCtx


instantiate :: Scheme a -> Infer a (Type a)
instantiate (Forall as t) = do
  let ann = typeAnn t
  as' <- mapM (const $ freshName >>= return . TyVar ann) as
  let s = M.fromList $ zip as as'
  return $ apply s t

generalize :: Context a -> Type a -> Scheme a
generalize ctx t = Forall as t
  where as = S.toList $ ftv t `S.difference` ftv ctx