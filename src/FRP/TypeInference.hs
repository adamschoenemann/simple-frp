
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}

module FRP.TypeInference where

import           Control.Monad.Except
import           Control.Monad.State
import           Control.Monad.RWS (RWST, tell, local, ask, runRWST)
import           Control.Monad.Identity
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

unScheme :: Scheme a -> Type a
unScheme (Forall _ ty) = ty

instance Pretty (Scheme a) where
  ppr n (Forall vs tau) =
    text "forall" <+> hcat (map text vs) <> char '.' <+> ppr 0 tau


type QualSchm t = (Scheme t, Qualifier)

newtype Context t = Ctx {unCtx :: Map Name (QualSchm t)} deriving (Show, Eq)

emptyCtx :: Context t
emptyCtx = Ctx M.empty

extend :: Context t -> (Name, QualSchm t) -> Context t
extend c (n, t) = Ctx $ M.insert n t $ unCtx c

remove :: Context t -> Name -> Context t
remove (Ctx m) x = Ctx $ M.delete x m

lookupCtx :: Name -> Infer t (Type t, Qualifier)
lookupCtx nm = do
  Ctx m <- ask
  case M.lookup nm m of
    Just (sc, q) -> do t <- instantiate sc
                       return (t, q)
    Nothing -> typeErr (UnknownIdentifier nm) (Ctx m)


instance Pretty (Context t) where
  ppr n (Ctx map) = vcat $ fmap mapper $ M.toList map where
    mapper (k, v) = text k <+> char ':' <+> ppr 0 v

newtype TyExcept t = TyExcept (TyErr t, Context t)
  deriving (Show, Eq)

data TyErr t
  = CannotUnify (QualSchm t) (QualSchm t) (Term t)
  | OccursCheckFailed Name (Type t)
  | UnknownIdentifier Name
  | NotSyntax (Term t)
  | TypeAnnRequired (Term t)
  | NotStableTy (QualSchm t)
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


-- newtype Infer t a = Infer (ExceptT (TyExcept t) (State [Name]) a)
--   deriving ( Functor, Applicative, Monad, MonadState [Name]
--            , MonadError (TyExcept t))

freshName :: Infer t Name
freshName = do
  nm:nms <- get
  put nms
  return nm


-- runInferTerm ctx t = runInfer (checkTerm ctx t)
-- runInferTerm' t = runInfer (checkTerm emptyCtx t)

runInfer :: Infer t a -> Either (TyExcept t) (a, [Constraint t])
runInfer inf =
  let r = runExcept (runRWST inf emptyCtx (infiniteSupply alphabet))
  in  noSnd <$> r
  where
    noSnd (a,b,c) = (a,c)
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
instance Substitutable (QualSchm a) a where
  apply st (ty, q) = (apply st ty, q)
  ftv (ty, q)      = ftv ty

instance Substitutable (Context a) a where
  apply s (Ctx ctx) = Ctx $ M.map (apply s) ctx
  ftv (Ctx ctx)     = foldr ((+++) . ftv) S.empty $ M.elems ctx

occursCheck :: Substitutable a b => TVar -> a -> Bool
occursCheck a t = a `S.member` ftv t


-- bind :: TVar -> Type a -> Infer a (Subst a)
-- bind a t | unitFunc t == TyVar () a = return nullSubst
--          | occursCheck a t = typeErr (OccursCheckFailed a t) emptyCtx
--          | otherwise       = return $ M.singleton a t

-- unify :: Type a -> Type a -> Infer a (Subst a)
-- unify type1 type2 = case (type1, type2) of

--   (TyArr _ l1 r1, TyArr _ l2 r2) -> do
--     s1 <- unify l1 l2
--     s2 <- unify (apply s1 r1) (apply s1 r2)
--     return (s2 `compose` s1)

--   (TyVar _ a, t) -> bind a t

--   (t, TyVar _ a) -> bind a t

--   (TyPrim _ p1, TyPrim _ p2) | p1 == p2 -> return nullSubst

--   (TyProd _a ll lr, TyProd _b rl rr) -> do
--     s1 <- unify ll rl
--     s2 <- unify rl rr
--     return (s2 `compose` s1)

--   (TySum  _a ll lr, TySum  _b rl rr) -> do
--     s1 <- unify ll rl
--     s2 <- unify rl rr
--     return (s2 `compose` s1)

--   (TyLater  _ lt, TyLater  _ rt) -> unify lt rt
--   (TyStable _ lt, TyStable _ rt) -> unify lt rt
--   (TyStream _ lt, TyStream _ rt) -> unify lt rt

--   (TyAlloc{}, TyAlloc{}) -> return nullSubst

--   (ty1, ty2) ->
--     let noterm = error "no term in function unify"
--         sig = Forall []
--     in  typeErr (CannotUnify (sig ty1, QNow) (sig ty2, QNow) noterm) emptyCtx


instantiate :: Scheme a -> Infer a (Type a)
instantiate (Forall as t) = do
  let ann = typeAnn t
  as' <- mapM (const $ freshName >>= return . TyVar ann) as
  let s = M.fromList $ zip as as'
  return $ apply s t

generalize :: Context a -> Type a -> Scheme a
generalize ctx t = Forall as t
  where as = S.toList $ ftv t `S.difference` ftv ctx

-- monad to do inference by constraint generation first and the solving
type Infer t a =
  (RWST (Context t)
        [Constraint t]
        InferState
        (Except (TyExcept t))
        a
  )

type Constraint t = (Type t, Type t)
type Unifier t = (Subst t, [Constraint t])

type Solve t a = StateT (Unifier t) (ExceptT (TyExcept t) Identity) a

type InferState = [String]
-- newtype InferState = InferState { count :: Int }

uni :: Type t -> Type t -> Infer t ()
uni t1 t2 = tell [(t1, t2)]

inEnv :: (Name, QualSchm t) -> Infer t a -> Infer t a
inEnv (x, sc) m = do
  let scope e = (remove e x) `extend` (x, sc)
  local scope m

inferNow :: Term t -> Infer t (Type t, Qualifier)
inferNow expr = do
  (t, q) <- infer expr
  ctx <- ask
  if (q == QNow)
    then return (t,q)
    else typeErr (NotNow expr) ctx

-- Consideration: Move logic that enforces qualifiers to be now/stbl/whatever
-- into the constraint solver? Could that be done? Is it better? Don't know yet
infer :: Term t -> Infer t (Type t, Qualifier)
infer = \case
  TmLit a (LInt _)  -> return (TyPrim a TyNat, QNow)
  TmLit a (LBool _) -> return (TyPrim a TyBool, QNow)

  TmVar a x -> lookupCtx x

  TmLam a x mty e -> do
    nm <- freshName
    let tv = TyVar a nm
    (t, q) <- inEnv (x, (Forall [] tv, QNow)) (inferNow e)
    return (TyArr a tv t, q)

  TmApp a e1 e2 -> do
    (t1, _) <- inferNow e1
    (t2, _) <- inferNow e2
    tv <- TyVar a <$> freshName
    uni t1 (TyArr a t2 tv)
    return (tv, QNow)

  TmLet a p e1 e2 -> do
    (t1, _) <- inferNow e1
    env2 <- inferPtn p t1
    local (const env2) (inferNow e2)



-- "Type check" a pattern. Basically, it unfold the pattern, makes sure
-- it matches the term, and then adds the appropriate names to the input context
inferPtn :: Pattern -> Type t -> Infer t (Context t)
inferPtn (PBind nm) ty = do
  ctx <- ask
  let sc = generalize ctx ty
  return $ ctx `extend` (nm, (sc, QNow))
inferPtn (PDelay nm) ty = do
  ctx <- ask
  let ann = typeAnn ty
  tv <- TyVar ann <$> freshName
  uni ty (TyLater ann tv)
  let sc = generalize ctx tv
  return $ ctx `extend` (nm, (sc, QLater))

-- inferPtn ptn sc = do
--   ctx <- ask
--   case ptn of
--     PBind nm  -> return $ ctx `extend` (nm, (sc, QNow))
--     PDelay nm -> do
--       let ann = typeAnn (unScheme sc)
--       tv <- TyVar ann <$> freshName
--       uni tv (TyLater a )

  -- go (PDelay nm) (TyLater a t, QNow) = return (extend nm (t, QLater) ctx)
  -- go (PCons hd tl) (TyStream a x, QNow) = do
  --   ctx1 <- inferPtn ctx hd (x, QNow)
  --   ctx2 <- inferPtn ctx1 tl (TyLater a (TyStream a x), QNow)
  --   return ctx2
  -- go (PStable p) (TyStable a t, QNow) = do
  --   ctx1 <- inferPtn ctx p (t, QStable)
  --   return ctx1
  -- go (PTup p1 p2) (TyProd a t1 t2, QNow) = do
  --   ctx1 <- inferPtn ctx  p1 (t1, QNow)
  --   ctx2 <- inferPtn ctx1 p2 (t2, QNow)
  --   return ctx2
  -- go p t = typeErr (CannotUnify undefined undefined undefined) ctx -- FIXME