
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}

module FRP.TypeInference where

import           Control.Monad.Except
import           Control.Monad.State
import           Control.Monad.RWS (RWST, tell, local, ask, runRWST, MonadReader)
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
import           Data.List (nub)


data Scheme a = Forall [TVar] (Type a)
  deriving (Eq, Functor)

unScheme :: Scheme a -> Type a
unScheme (Forall _ ty) = ty

toScheme :: Type a -> Scheme a
toScheme = Forall []

instance Pretty (Scheme a) where
  ppr n (Forall [] tau) = ppr n tau
  ppr n (Forall vs tau) =
    text "forall" <+> hcat (punctuate space $ map text vs) <> char '.' <+> ppr 0 tau

instance Show (Scheme a) where
  show = ppshow


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

isStable :: Type t -> Bool
isStable (TyPrim _ _ )  = True
isStable (TyProd _ a b) = isStable a && isStable b
isStable (TySum  _ a b) = isStable a && isStable b
isStable (TyStable _ _) = True
isStable _              = False

instance Pretty (Context t) where
  ppr n (Ctx map) = vcat $ fmap mapper $ M.toList map where
    mapper (k, v) = text k <+> char ':' <+> ppr 0 v

newtype TyExcept t = TyExcept (TyErr t, Context t)
  deriving (Show, Eq)

data TyErr t
  = CannotUnify (Type t) (Type t) (Unifier t)
  | UnificationMismatch [Type t] [Type t]
  | OccursCheckFailed Name (Type t)
  | UnknownIdentifier Name
  | NotSyntax (Term t)
  | TypeAnnRequired (Term t)
  | NotStableTy (Type t)
  | NotStable (Term t)
  | NotNow (Term t)
  | NotLater (Term t)
  deriving (Show, Eq)

instance Pretty (TyExcept t) where
  ppr n (TyExcept (err, ctx)) = ppr n err $$ text "in context: " $$ ppr n ctx

instance Pretty (TyErr t) where
  ppr n = \case
    CannotUnify t1 t2 unif ->
      text "Cannot unify expected type"
            <+> ppr 0 t1
            <+> text "with"
            <+> ppr 0 t2
            <+> text "at" $$ ppr 0 unif

    UnificationMismatch t1 t2 ->
      text "UnificationMismatch: "
            <+> hcat (punctuate (char ',') $ map (ppr 0) t1)
            <+> text "with"
            <+> hcat (punctuate (char ',') $ map (ppr 0) t2)

    OccursCheckFailed nm ty -> text nm <+> "occurs in" <+> (ppr 0 ty)
    UnknownIdentifier nm    -> text "unkown identifier" <+> text nm
    NotSyntax trm           -> ppr 0 trm <+> "is not syntax"
    TypeAnnRequired trm     -> ppr 0 trm <+> text "requires a type annotation"
    NotStableTy ty          -> text "expected" <+> ppr n ty  <+> text "to be a stable type"
    NotNow    trm           -> text "expected" <+> ppr n trm <+> text "to be now"
    NotLater  trm           -> text "expected" <+> ppr n trm <+> text "to be later"
    NotStable trm           -> text "expected" <+> ppr n trm <+> text "to be stable"

typeErr :: MonadError (TyExcept t) m
        => TyErr t -> Context t -> m a
typeErr err ctx = throwError (TyExcept (err, ctx))

typeErr' :: (MonadError (TyExcept t) m, MonadReader (Context t) m)
         => TyErr t -> m a
typeErr' err = do
  ctx <- ask
  throwError (TyExcept (err, ctx))


-- newtype Infer t a = Infer (ExceptT (TyExcept t) (State [Name]) a)
--   deriving ( Functor, Applicative, Monad, MonadState [Name]
--            , MonadError (TyExcept t))

-- syntax highlighting is being a bitch so I added braces
freshName :: Infer t Name
freshName =
  do {
    nm:nms <- get;
    put nms;
    return nm
  }


-- runInferTerm ctx t = runInfer (checkTerm ctx t)
-- runInferTerm' t = runInfer (checkTerm emptyCtx t)

letters :: [String]
letters = infiniteSupply alphabet where
  infiniteSupply supply = supply ++ addSuffixes supply (1 :: Integer)
  alphabet = map (:[]) ['a'..'z']
  addSuffixes xs n = (map (\x -> addSuffix x n) xs) ++ (addSuffixes xs (n+1))
  addSuffix x n = x ++ show n

runInfer' :: Infer t a -> Either (TyExcept t) (a, [Constraint t])
runInfer' = runInfer emptyCtx

runInfer :: Context t -> Infer t a -> Either (TyExcept t) (a, [Constraint t])
runInfer ctx inf =
  let r = runExcept (runRWST inf ctx letters)
  in  noSnd <$> r
  where
    noSnd (a,b,c) = (a,c)


type TVar = Name
type Subst a = Map TVar (Type a)

instance Pretty (Subst a) where
  ppr n map = vcat $ fmap mapper $ M.toList map where
    mapper (k, v) = text k <+> char ':' <+> ppr 0 v

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
    TyProd   a l r    -> TyProd   a (apply st l) (apply st r)
    TySum    a l r    -> TySum    a (apply st l) (apply st r)
    TyArr    a t1 t2  -> TyArr    a (apply st t1) (apply st t2)
    TyLater  a ty     -> TyLater  a (apply st ty)
    TyStable a ty     -> TyStable a (apply st ty)
    TyStream a ty     -> TyStream a (apply st ty)
    TyRec    a nm ty  -> TyRec    a nm (apply st ty) -- FIXME: Is this correct?
    TyAlloc  a        -> TyAlloc  a
    TyPrim{}          -> typ

  ftv = \case
    TyVar    _ name   -> S.singleton name
    TyProd   _ l r    -> ftv l  +++ ftv r
    TySum    _ l r    -> ftv l  +++ ftv r
    TyArr    _ t1 t2  -> ftv t1 +++ ftv t2
    TyLater  _ ty     -> ftv ty
    TyStable _ ty     -> ftv ty
    TyStream _ ty     -> ftv ty
    TyRec    _ nm ty  -> S.delete nm $ ftv ty
    TyAlloc  _        -> S.empty
    TyPrim{}          -> S.empty

instance Substitutable (Scheme a) a where
  apply st (Forall vs t) =
    let st' = foldr M.delete st vs
    in  Forall vs $ apply st' t

  ftv (Forall vs t) = ftv t `S.difference` S.fromList vs

instance Substitutable (f a) a => Substitutable [f a] a  where
  apply = fmap . apply
  ftv   = foldr ((+++) . ftv) S.empty

instance Substitutable (QualSchm a) a where
  apply st (ty, q) = (apply st ty, q)
  ftv (ty, q)      = ftv ty

instance Substitutable (Context a) a where
  apply s (Ctx ctx) = Ctx $ M.map (apply s) ctx
  ftv (Ctx ctx)     = foldr ((+++) . ftv) S.empty $ M.elems ctx

instance Substitutable (Constraint a) a where
   apply s (Constraint (t1, t2)) = Constraint (apply s t1, apply s t2)
   ftv (Constraint (t1, t2)) = ftv t1 +++ ftv t2

occursCheck :: Substitutable a b => TVar -> a -> Bool
occursCheck a t = a `S.member` ftv t


bind :: TVar -> Type a -> Solve a (Unifier a)
bind a t | unitFunc t == TyVar () a = return emptyUnifier
         | occursCheck a t = typeErr (OccursCheckFailed a t) emptyCtx
         | otherwise       = return $ Unifier (M.singleton a t, [])

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

type InferState = [String]

type Infer t a =
  (RWST (Context t)
        [Constraint t]
        InferState
        (Except (TyExcept t))
        a
  )

newtype Constraint t = Constraint (Type t, Type t)
  deriving (Eq)

instance Functor Constraint where
  fmap f (Constraint (a,b)) = Constraint (fmap f a, fmap f b)

instance Pretty (Constraint a) where
  ppr n (Constraint (t1, t2)) = ppr n t1 <+> text ".=." <+> ppr n t2

instance Pretty [Constraint a] where
  ppr n cs = vcat $ map (ppr 0) cs

instance Show (Constraint a) where
  show = ppshow


infixr 0 .=.
(.=.) :: Type t -> Type t -> Constraint t
t1 .=. t2 = Constraint (t1, t2)

newtype Unifier t = Unifier (Subst t, [Constraint t])
  deriving (Eq, Show, Functor)

instance Pretty (Unifier t) where
  ppr n (Unifier (st, cs)) =
    text "subst:" <+> ppr 0 st $$
    text "constraints:" $$ nest 2 (ppr 0 cs)

emptyUnifier :: Unifier t
emptyUnifier = Unifier (nullSubst, [])

newtype Solve t a = Solve (StateT (Unifier t) (Except (TyExcept t)) a)
  deriving ( Functor, Monad, MonadState (Unifier t)
           , MonadError (TyExcept t), Applicative
           )

runSolve :: Unifier t -> Either (TyExcept t) (Subst t, Unifier t)
runSolve un = runExcept (runStateT (unSolver solver) un) where
  unSolver (Solve m) = m

inferTerm' :: Term t -> Either (TyExcept t) (QualSchm t)
inferTerm' = inferTerm emptyCtx

inferTerm :: Context t -> Term t -> Either (TyExcept t) (QualSchm t)
inferTerm ctx trm = case runInfer ctx (infer trm) of
  Left err -> Left err
  Right ((ty,q), cs) -> case runSolve (un cs) of
    Left err -> Left err
    Right (subst, unies) -> Right $ (closeOver $ apply subst ty, q)
  where
    closeOver = normalize . generalize emptyCtx
    un cs = Unifier (nullSubst, cs)


unifies :: Type t -> Type t -> Solve t (Unifier t)
unifies t1 t2 | unitFunc t1 == unitFunc t2 = return emptyUnifier
unifies (TyVar _ v) t = v `bind` t
unifies t (TyVar _ v) = v `bind` t
unifies (TyArr _ t1 t2) (TyArr _ t3 t4) = unifyMany [t1,t2] [t3,t4]
unifies (TyStable _ t1) (TyStable _ t2) = t1 `unifies` t2
unifies (TyLater _ t1) (TyLater _ t2)   = t1 `unifies` t2
unifies (TyStream _ t1) (TyStream _ t2) = t1 `unifies` t2
unifies t1 t2 = do
  unif <- get
  typeErr (CannotUnify t1 t2 unif) emptyCtx

unifyMany :: [Type t] -> [Type t] -> Solve t (Unifier t)
unifyMany [] [] = return emptyUnifier
unifyMany (t1 : ts1) (t2 : ts2) =
  do Unifier (su1, cs1) <- unifies t1 t2
     Unifier (su2, cs2) <- unifyMany (apply su1 ts1) (apply su1 ts2)
     return $ Unifier (su2 `compose` su1, cs1 ++ cs2)
unifyMany t1 t2 = typeErr (UnificationMismatch t1 t2) emptyCtx

solver :: Solve t (Subst t)
solver = do
  Unifier (su, cs) <- get
  case cs of
    [] -> return su
    (Constraint (t1,t2) : cs0) -> do
      Unifier (su1, cs1) <- unifies t1 t2
      put $ Unifier (su1 `compose` su, cs1 ++ (apply su1 cs0))
      solver

uni :: Type t -> Type t -> Infer t ()
uni t1 t2 = tell [Constraint (t1, t2)]

unionCtx :: Context t -> Context t -> Context t
unionCtx (Ctx c1) (Ctx c2) = Ctx (c1 `M.union` c2)

mapCtx :: (QualSchm t -> QualSchm t) -> Context t -> Context t
mapCtx fn (Ctx m) = Ctx (M.map fn m)

laterCtx :: Context t -> Context t
laterCtx (Ctx c1) =
  Ctx $ M.map (maybe (error "laterCtx") (id)) $ M.filter isJust $ M.map mapper c1 where
    mapper (t,q) = case q of
      QNow -> Nothing
      QStable -> Just (t, QStable)
      QLater  -> Just (t, QNow)

stableCtx :: Context t -> Context t
stableCtx (Ctx c1) =
  Ctx $ M.map (maybe (error "laterCtx") (id)) $ M.filter isJust $ M.map mapper c1 where
    mapper (t,q) = case q of
      QNow -> Nothing
      QStable -> Just (t, QStable)
      QLater  -> Nothing

inCtx :: (Name, QualSchm t) -> Infer t a -> Infer t a
inCtx (x, sc) m = local scope m where
  scope e = (remove e x) `extend` (x, sc)

inStableCtx :: (Name, QualSchm t) -> Infer t a -> Infer t a
inStableCtx (x, sc) m = local scope m where
  scope ctx = (stableCtx . remove ctx $ x) `extend` (x, sc)

inferNow :: Term t -> Infer t (Type t, Qualifier)
inferNow expr = do
  (t, q) <- infer expr
  ctx <- ask
  if (q == QNow || q == QStable)
    then return (t,QNow)
    else typeErr (NotNow expr) ctx

inferLater :: Term t -> Infer t (Type t, Qualifier)
inferLater expr = do
  ctx0 <- ask
  (t, q) <- local laterCtx $ infer expr
  if (q == QNow)
    then return (t,q)
    else typeErr (NotLater expr) ctx0

inferStable :: Term t -> Infer t (Type t, Qualifier)
inferStable expr = do
  ctx0 <- ask
  (t, q) <- local stableCtx $ infer expr
  if (q == QStable)
    then return (t,q)
    else typeErr (NotStable expr) ctx0

-- Consideration: Move logic that enforces qualifiers to be now/stbl/whatever
-- into the constraint solver? Could that be done? Is it better? Don't know yet
infer :: Term t -> Infer t (Type t, Qualifier)
infer term = case term of
  TmLit a (LInt _)  -> return (TyPrim a TyNat, QNow)
  TmLit a (LBool _) -> return (TyPrim a TyBool, QNow)
  TmAlloc a         -> return (TyAlloc a, QNow)
  TmPntr a l        -> typeErr' (NotSyntax term)
  TmPntrDeref a l   -> typeErr' (NotSyntax term)

  TmFst a e -> do
    (t1, _) <- inferNow e
    tv1 <- TyVar a <$> freshName
    tv2 <- TyVar a <$> freshName
    uni t1 (TyProd a tv1 tv2)
    return (tv1, QNow)

  TmSnd a e -> do
    (t1, _) <- inferNow e
    tv1 <- TyVar a <$> freshName
    tv2 <- TyVar a <$> freshName
    uni t1 (TyProd a tv1 tv2)
    return (tv2, QNow)

  TmTup a e1 e2 -> do
    (t1, _) <- inferNow e1
    (t2, _) <- inferNow e2
    return (TyProd a t1 t2, QNow)

  TmVar a x -> lookupCtx x

  -- FIXME: for now, we ignore the maybe type signature on the lambda
  TmLam a x mty e -> do
    tv <- TyVar a <$> freshName
    (t, q) <- inCtx (x, (Forall [] tv, QNow)) (inferNow e)
    return (TyArr a tv t, q)

  TmApp a e1 e2 -> do
    (t1, _) <- inferNow e1
    (t2, _) <- inferNow e2
    tv <- TyVar a <$> freshName
    uni t1 (TyArr a t2 tv)
    return (tv, QNow)

  TmLet a p e1 e2 -> do
    (t1, _) <- inferNow e1
    ctx2 <- inferPtn p t1
    local (`unionCtx` ctx2) (inferNow e2)

  -- FIXME: we ignore type signatures
  TmFix a x mty e -> do
    tv <- TyVar a <$> freshName
    (t, q) <- inStableCtx (x, (Forall [] tv, QLater)) (inferNow e)
    uni tv t
    return (tv, QNow)

  TmBinOp a op e1 e2 -> do
    (t1, q1) <- inferNow e1
    (t2, q2) <- inferNow e2
    tv <- TyVar a <$> freshName
    let u1 = TyArr a t1 (TyArr a t2 tv)
        u2 = binOpTy a op
    uni u1 u2
    return (tv, QNow)

  TmITE a cond tr fl -> do
    (t1,q1) <- inferNow cond
    (t2,q2) <- inferNow tr
    (t3,q3) <- inferNow fl
    uni t1 (TyPrim a TyBool)
    uni t2 t3
    return (t2, QNow)

  TmCons a hd tl -> do
    (t1,q1) <- inferNow hd
    (t2,q2) <- inferNow tl
    tv <- TyVar a <$> freshName
    uni t2 (TyLater a (TyStream a t1))
    uni tv (TyStream a t1)
    return (tv, QNow)

  TmPromote a e -> do
    (t1, _) <- inferNow e
    tv <- TyVar a <$> freshName
    uni tv (TyStable a t1)
    return (tv, QNow)

  TmStable a e -> do
    (t1, _) <- inferStable e
    tv <- TyVar a <$> freshName
    uni tv (TyStable a t1)
    return (tv, QNow)

  TmDelay a u e -> do
    (tu, _) <- inferNow u
    uni tu (TyAlloc a)
    (te, _) <- inferLater e
    tv <- TyVar a <$> freshName
    uni tv (TyLater a te)
    return (tv, QNow)

  TmInl a e -> do
    (ty, _) <- inferNow e
    tv <- TyVar a <$> freshName
    tvr <- TyVar a <$> freshName
    uni tv (TySum a ty tvr)
    return (tv, QNow)

  TmInr a e -> do
    (ty, _) <- inferNow e
    tv <- TyVar a <$> freshName
    tvl <- TyVar a <$> freshName
    uni tv (TySum a tvl ty)
    return (tv, QNow)

  TmCase a e (nm1, c1) (nm2, c2) -> do
    (ty, _) <- inferNow e
    tvl <- TyVar a <$> freshName
    tvr <- TyVar a <$> freshName
    uni ty (TySum a tvl tvr)
    (t1, _) <- inCtx (nm1, (Forall [] tvl, QNow)) $ inferNow c1
    (t2, _) <- inCtx (nm2, (Forall [] tvr, QNow)) $ inferNow c2
    uni t1 t2
    return (t1, QNow)

  TmInto a e -> do
    (ty, _) <- inferNow e
    alpha <- freshName
    tv <- TyVar a <$> freshName
    uni tv (apply (M.singleton alpha (TyLater a $ TyRec a alpha ty)) ty)
    return (tv, QNow)

  TmOut a e -> do
    (rty, _) <- inferNow e
    alpha <- freshName
    tv <- TyVar a <$> freshName
    uni rty (TyRec a alpha tv)
    let ty = apply (M.singleton alpha (TyLater a $ TyRec a alpha rty)) rty
    return (ty, QNow)

  where
    binOpTy :: a -> BinOp -> Type a -- (Type a, Type a, Type a)
    binOpTy a =
      let fromPrim (x,y,z) = (TyPrim a x, TyPrim a y, TyPrim a z)
          toArr (x,y,z)    = TyArr a y (TyArr a z x)
          primArr = toArr . fromPrim
      in  \case
        --               ret     left    right
        Add  -> primArr (TyNat , TyNat , TyNat )
        Sub  -> primArr (TyNat , TyNat , TyNat )
        Mult -> primArr (TyNat , TyNat , TyNat )
        Div  -> primArr (TyNat , TyNat , TyNat )
        And  -> primArr (TyBool, TyBool, TyBool)
        Or   -> primArr (TyBool, TyBool, TyBool)
        Leq  -> primArr (TyBool, TyNat , TyNat )
        Lt   -> primArr (TyBool, TyNat , TyNat )
        Geq  -> primArr (TyBool, TyNat , TyNat )
        Gt   -> primArr (TyBool, TyNat , TyNat )
        Eq   -> primArr (TyBool, TyNat , TyNat )

-- "Type check" a pattern. Basically, it unfold the pattern, makes sure
-- it matches the term, and then returns a context with all the bound names
-- Let generalization makes this hard. It works right now, but I'm pretty
-- sure it is not correct. Ask your supervisors!
inferPtn :: Pattern -> Type t -> Infer t (Context t)
inferPtn pattern ty = case pattern of

  PBind nm -> do
    ctx <- ask
    let sc = generalize ctx ty
    return $ Ctx $ M.singleton nm (sc, QNow)

  PDelay nm -> do
    ctx <- ask
    let ann = typeAnn ty
    fnm <- freshName
    let tv = TyVar ann fnm
    uni ty (TyLater ann tv)
    -- instantiate out the tv itself from the generalization
    -- not sure if correct, just a hack that works for now
    -- and perhaps it should simply not be generalized at all
    let sc@(Forall vs _) = generalize ctx tv
    let vs' = filter (/= fnm) vs
    return $ Ctx $ M.singleton nm (Forall vs' tv, QLater)

  PCons hd tl -> do
    let ann = typeAnn ty
    hnm <- freshName
    tnm <- freshName
    let htv = TyVar ann hnm
    let ttv = TyVar ann tnm
    uni ty (TyStream ann htv)
    uni ttv (TyLater ann ty)
    ctx1 <- inCtx (hnm, (Forall [] htv, QNow)) (inferPtn hd htv)
    ctx2 <- inCtx (tnm, (Forall [] ttv, QNow)) (inferPtn tl ttv)
    return (ctx1 `unionCtx` ctx2)

  PStable p -> do
    let ann = typeAnn ty
    nm <- freshName
    let tv = TyVar ann nm
    uni ty (TyStable ann tv)
    ctx1 <- inCtx (nm, (Forall [] tv, QNow)) $ inferPtn p tv
    return $ mapCtx (\(t,q) -> (t,QStable)) ctx1

  PTup p1 p2 -> do
    let ann = typeAnn ty
    nm1 <- freshName
    nm2 <- freshName
    let tv1 = TyVar ann nm1
    let tv2 = TyVar ann nm2
    uni ty (TyProd ann tv1 tv2)
    ctx1 <- inCtx (nm1, (Forall [] tv1, QNow)) $ inferPtn p1 tv1
    ctx2 <- inCtx (nm2, (Forall [] tv2, QNow)) $ inferPtn p2 tv2
    return (ctx1 `unionCtx` ctx2)

-- normalize a type-scheme in the sense that we rename all the
-- type variables to be in alphabetical order of occurence
normalize :: Scheme t -> Scheme t
normalize (Forall _ body) = Forall (map snd ord) (normtype body)
  where
    ord = zip (nub $ S.toList $ ftv body) (letters)

    normtype ty = case ty of
      TyProd   a l r    -> TyProd a (normtype l) (normtype r)
      TySum    a l r    -> TySum a (normtype l) (normtype r)
      TyArr    a l r    -> TyArr a (normtype l) (normtype r)
      TyLater  a ty     -> TyLater a (normtype ty)
      TyStable a ty     -> TyStable a (normtype ty)
      TyStream a ty     -> TyStream a (normtype ty)
      TyRec    a nm ty  -> TyRec a nm (normtype ty)
      TyAlloc  a        -> ty
      TyPrim{}          -> ty

      TyVar    a name   ->
        case Prelude.lookup name ord of
          Just x -> TyVar a x
          Nothing -> error "type variable not in signature"