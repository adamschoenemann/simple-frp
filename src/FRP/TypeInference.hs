{-|
Module      : FRP.TypeInference
Description : Type inference

This module defines an inference algorithm to infer the types of a
term\/declaration\/program and subsequently typecheck them.
-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TupleSections              #-}

module FRP.TypeInference (
    Scheme(..)
  , toScheme
  , Context(..)
  , emptyCtx
  , Constraint(..)
  , QualSchm
  , StableTy(..)
  , (.=.)
  , TyExcept(..)
  , InferWrite
  , infer
  , inferTerm
  , inferTerm'
  , inferDecl
  , inferDecl'
  , inferProg
  , runInfer
  , runInfer'
  , solveInfer
  ) where

import           Control.Monad.Except
import           Control.Monad.Identity
import           Control.Monad.RWS      ( MonadReader, RWST, ask, local, runRWST
                                        , tell, MonadWriter)
import           Control.Monad.State
import           Data.List              (nub, find)
import           Data.Map.Strict        (Map)
import qualified Data.Map.Strict        as M
import           Data.Maybe             (isJust)
import           Data.Set               (Set)
import qualified Data.Set               as S
import           Debug.Trace
import           FRP.AST
import           FRP.AST.Construct      (tmvar)
import           FRP.Pretty
import           Data.Bifunctor (bimap)


-- |A type-variable is just a name
type TVar = Name

-- |A class for monads that can generate fresh names
class NameGen m where
  freshName :: m String

-- |An infinite supply of one-letter variable names.
-- The names are prefixed with [0..], making them syntactically invalid.
-- This prevents the user from ever introducing such a name, making them
-- automatically fresh.
letters :: [String]
letters = infiniteSupply alphabet where
  infiniteSupply supply = addPrefixes supply (0 :: Integer)
  alphabet = map (:[]) ['a'..'z']
  addPrefixes xs n = (map (\x -> addPrefix x n) xs) ++ (addPrefixes xs (n+1))
  addPrefix x n = show n ++ x

{-|
  A substitution is just a mapping from type-variables to their \'actual\' types
-}
type Subst t = Map TVar (Type t)

instance Pretty (Subst a) where
  ppr n map = vcat $ fmap mapper $ M.toList map where
    mapper (k, v) = text k <+> char ':' <+> ppr 0 v

-- |The empty substitution
nullSubst :: Subst a
nullSubst = M.empty

{-|
  Something that can be substituted means that you can apply a substitution
  to it, and you can get the free type-variables.
  The functional dependency arises from the fact that we want to instance
  types of kind * -> *, since we have parameterized the type of annotations
  on types and terms.
-}
class Substitutable a t | a -> t where
  apply :: Subst t -> a -> a
  ftv   :: a -> Set TVar

{-|
  You can compose two substitutions s1, s2 by applying s1 to everything in
  s2 and also keeping the substitutions in s1.
  @
    s1 = M.fromList [("a", tynat), ("b", tybool)]
    s2 = M.fromList [("c", "a" |-> tynat)]
    s1 `compose` s2 == M.fromList [ ("c", tynat |-> tynat)
                                  , ("b", tybool)
                                  , ("a", tynat)
                                  ]
  @
-}
compose :: Subst a -> Subst a -> Subst a
s1 `compose` s2 = M.map (apply s1) s2 `M.union` s1

-- |Just to use S.union infix a bit easier
(+++) = S.union

-- |You can substitute lists of substitutables
instance Substitutable (f a) a => Substitutable [f a] a  where
  apply = fmap . apply
  ftv   = foldr ((+++) . ftv) S.empty

-- |Types are substitutable
instance Substitutable (Type a) a where
  apply st typ = case typ of
    TyVar    a name  -> M.findWithDefault typ name st
    TyProd   a l r   -> TyProd   a (apply st l) (apply st r)
    TySum    a l r   -> TySum    a (apply st l) (apply st r)
    TyArr    a t1 t2 -> TyArr    a (apply st t1) (apply st t2)
    TyLater  a ty    -> TyLater  a (apply st ty)
    TyStable a ty    -> TyStable a (apply st ty)
    TyStream a ty    -> TyStream a (apply st ty)
    TyRec    a nm ty -> TyRec    a nm (apply st ty) -- FIXME: Is this correct?
    TyAlloc  a       -> TyAlloc  a
    TyPrim{}         -> typ

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


-- |A quantified (forall) type
data Scheme a = Forall [TVar] (Type a)
  deriving (Eq, Functor)

-- |Get the underlying type of the scheme
unScheme :: Scheme a -> Type a
unScheme (Forall _ ty) = ty

-- |Promote a type to a zero-quantified scheme
toScheme :: Type a -> Scheme a
toScheme = Forall []

instance Pretty (Scheme a) where
  ppr n (Forall [] tau) = ppr n tau
  ppr n (Forall vs tau) =
    text "forall" <+> hcat (punctuate space $ map text vs) <> char '.' <+> ppr 0 tau

instance Show (Scheme a) where
  show = ppshow

instance Substitutable (Scheme a) a where
  apply st (Forall vs t) =
    let st' = foldr M.delete st vs
    in  Forall vs $ apply st' t

  ftv (Forall vs t) = ftv t `S.difference` S.fromList vs

-- |A scheme and a 'Qualifier'
type QualSchm t = (Scheme t, Qualifier)

-- |Qualified schemes are substitutable
instance Substitutable (QualSchm a) a where
  apply st (ty, q) = (apply st ty, q)
  ftv (ty, q)      = ftv ty

-- |A type context is a map from names to 'QualSchm's
newtype Context t = Ctx {unCtx :: Map Name (QualSchm t)} deriving (Show, Eq)

instance Pretty (Context t) where
  ppr n (Ctx map) = vcat $ fmap mapper $ M.toList map where
    mapper (k, v) = text k <+> char ':' <+> ppr 0 v

instance Substitutable (Context a) a where
  apply s (Ctx ctx) = Ctx $ M.map (apply s) ctx
  ftv (Ctx ctx)     = foldr ((+++) . ftv) S.empty $ M.elems ctx

-- |The empty context
emptyCtx :: Context t
emptyCtx = Ctx M.empty

-- |Extend a context with a 'Name' and a 'QualSchm'
extend :: Context t -> (Name, QualSchm t) -> Context t
extend c (n, t) = Ctx $ M.insert n t $ unCtx c

-- |Remove a name from a context
remove :: Context t -> Name -> Context t
remove (Ctx m) x = Ctx $ M.delete x m

{-|
  Lookup the type of a name in the context.
  If the name is not in the context, it will throw an 'UnknownIdentifier' error.
  If the associated qualifier is not 'QNow' or 'QStable', it will return a
  'DelayedUse' exception.
-}
lookupCtx :: Name -> Infer t (Type t)
lookupCtx nm = do
  Ctx m <- ask
  case M.lookup nm m of
    Just (sc, q) | q == QNow || q == QStable ->
      do t <- instantiate sc
         return t
    Just (sc, q) -> typeErr (DelayedUse nm) (Ctx m)
    Nothing -> typeErr (UnknownIdentifier nm) (Ctx m)

-- |A type exception is a type-error and an associated type context
newtype TyExcept t = TyExcept (TyErr t, Context t)
  deriving (Eq)

instance Show (TyExcept t) where
  show = ppshow

instance Pretty (TyExcept t) where
  ppr n (TyExcept (err, ctx)) = ppr n err $$ text "in context: " $$ ppr n ctx

-- |An error that can happen during type inference
data TyErr t
  = CannotUnify (Type t) (Type t) (Unifier t)
  | UnificationMismatch [Type t] [Type t]
  | OccursCheckFailed Name (Type t) (Unifier t)
  | UnknownIdentifier Name
  | NotSyntax (Term t)
  | TypeAnnRequired (Term t)
  | NotStableTy (Type t)
  | NotStable (Term t)
  | NotNow (Term t)
  | NotLater (Term t)
  | DelayedUse Name
  deriving (Show, Eq)

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

    OccursCheckFailed nm ty unif ->
      text nm <+> "occurs in" <+> (ppr 0 ty)
              <+> text "at" $$ ppr 0 unif

    UnknownIdentifier nm    -> text "unkown identifier" <+> text nm
    NotSyntax trm           -> ppr 0 trm <+> "is not syntax"
    TypeAnnRequired trm     -> ppr 0 trm <+> text "requires a type annotation"
    NotStableTy ty          -> text "expected" <+> ppr n ty  <+> text "to be a stable type"
    NotNow    trm           -> text "expected" <+> ppr n trm <+> text "to be now"
    NotLater  trm           -> text "expected" <+> ppr n trm <+> text "to be later"
    NotStable trm           -> text "expected" <+> ppr n trm <+> text "to be stable"
    DelayedUse name         -> text "cannot use delayed name" <+> text name

-- |Throw a type error in a context
typeErr :: MonadError (TyExcept t) m
        => TyErr t -> Context t -> m a
typeErr err ctx = throwError (TyExcept (err, ctx))

-- |Throw a type error, getting the context from the reader monad
typeErrM :: (MonadError (TyExcept t) m, MonadReader (Context t) m)
         => TyErr t -> m a
typeErrM err = do
  ctx <- ask
  throwError (TyExcept (err, ctx))


-- |Checks if a type variable occurs in a type signature.
-- If it does, then unification would never terminate.
occursCheck :: Substitutable a b => TVar -> a -> Bool
occursCheck a t = a `S.member` ftv t

-- |Bind a type-variable to a type
-- Throws an OccursCheckFailed error if the variable occurs in type to be bound.
bind :: TVar -> Type a -> Solve a (Unifier a)
bind a t | unitFunc t == TyVar () a = return emptyUnifier
         | occursCheck a t = do
              unif <- getUni
              typeErr (OccursCheckFailed a t unif) emptyCtx
         | otherwise       = return $ Unifier (M.singleton a t, [])

-- |Instantiates a 'Scheme' with fresh type variables, making a mono-type
-- out of a poly-type
instantiate :: Scheme a -> Infer a (Type a)
instantiate (Forall as t) = do
  let ann = typeAnn t
  as' <- mapM (const $ freshName >>= return . TyVar ann) as
  let s = M.fromList $ zip as as'
  return $ apply s t

generalize :: Context a -> Type a -> Scheme a
generalize ctx t = Forall as t
  where as = S.toList $ ftv t `S.difference` ftv ctx

-- |The state of infer is just a list of fresh names
type InferState = [Name]

-- |An Infer monad writes a list of unification constraints and a list
-- of types that should be stable
type InferWrite t = ([Constraint t], [StableTy t])

-- |Monad that generates unification constraints to be solved later
newtype Infer t a = Infer
  {unInfer :: RWST (Context t) (InferWrite t) InferState
                   (Except (TyExcept t)) a
  }
  deriving ( Functor, Monad, MonadState (InferState)
           , MonadReader (Context t), MonadWriter (InferWrite t)
           , MonadError (TyExcept t), Applicative
           )

instance NameGen (Infer t) where
  freshName =
    do nm:nms <- get
       put nms
       return nm

-- |Run an infer in the empty context, and forget about the state of the freshnames
runInfer' :: Infer t a -> Either (TyExcept t) (a, InferWrite t)
runInfer' inf = noSnd <$> runInfer emptyCtx inf
  where
    noSnd (a,b,c) = (a,c)

-- |Run an infer in a given context
-- Remember that the InferState returned is going to be infinite, so don't try
-- to print it ;)
runInfer :: Context t -> Infer t a -> Either (TyExcept t) (a, InferState, InferWrite t)
runInfer ctx inf =
  runExcept (runRWST (unInfer inf) ctx letters)

-- -----------------------------------------------------------------------------
-- | A 'Constraint' represents that two types should unify
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

instance Substitutable (Constraint a) a where
   apply s (Constraint (t1, t2)) = Constraint (apply s t1, apply s t2)
   ftv (Constraint (t1, t2)) = ftv t1 +++ ftv t2


-- -----------------------------------------------------------------------------
-- |A 'StableTy' represents that a type should be stable
newtype StableTy t = StableTy { unStableTy :: (Type t) }
  deriving (Eq)

instance Functor StableTy where
  fmap f (StableTy t) = StableTy (fmap f t)

instance Pretty (StableTy a) where
  ppr n (StableTy t) = ppr n t <+> "should be stable"

instance Pretty [StableTy a] where
  ppr n cs = vcat $ map (ppr 0) cs

instance Show (StableTy a) where
  show = ppshow

instance Substitutable (StableTy a) a where
   apply s (StableTy t) = StableTy (apply s t)
   ftv (StableTy t) = ftv t

-- |Infix constructor for unification constraints
infixr 0 .=.
(.=.) :: Type t -> Type t -> Constraint t
t1 .=. t2 = Constraint (t1, t2)


-- -----------------------------------------------------------------------------
-- |A 'Unifier' is a substitution that will yield the principal type
-- that satisfies the constraints, or fail
newtype Unifier t = Unifier (Subst t, [Constraint t])
  deriving (Eq, Show, Functor)

instance Pretty (Unifier t) where
  ppr n (Unifier (st, cs)) =
    text "subst:" <+> ppr 0 st $$
    text "constraints:"  $$ nest 2 (ppr 0 cs)

emptyUnifier :: Unifier t
emptyUnifier = Unifier (nullSubst, [])

-- -----------------------------------------------------------------------------
-- |The state of the solver is a unifier and a supply of fresh names
type SolveState t = (Unifier t, [Name])

-- |The 'Solve' monad is a stack of a state-monad with 'SolveState' and
-- an exception monad that throws 'TyExcept's
newtype Solve t a = Solve (StateT (SolveState t) (Except (TyExcept t)) a)
  deriving ( Functor, Monad, MonadState (SolveState t)
           , MonadError (TyExcept t), Applicative
           )

-- |Solve can generate fresh names
instance NameGen (Solve t) where
  freshName =
    do nm:nms <- snd <$> get
       modify (\(u,_) -> (u, nms))
       return nm

-- |Run a Solve monad. Supply list of fresh names and a starting unifier
runSolve :: [String] -> Unifier t -> Either (TyExcept t) (Subst t, Unifier t)
runSolve names un = bimap id rmNames $  runExcept (runStateT (unSolver solver) (un, names))
  where
    rmNames e = let (s, (u, _)) = e in (s, u)
    unSolver (Solve m) = m

-- |Infer a term in the empty typing context
inferTerm' :: Term t -> Either (TyExcept t) (Scheme t)
inferTerm' = inferTerm emptyCtx

-- |Infer a term in a given typing context
inferTerm :: Context t -> Term t -> Either (TyExcept t) (Scheme t)
inferTerm ctx trm = solveInfer ctx (infer trm)

-- |Infer a declaration in the empty typing context
inferDecl' :: Decl t -> Either (TyExcept t) (Scheme t)
inferDecl' = inferDecl emptyCtx

-- |Infer a declaration in a given context
inferDecl :: Context t -> Decl t -> Either (TyExcept t) (Scheme t)
inferDecl ctx decl = solveInfer ctx declInfer where
  declInfer =
    do t <- infer (_body decl)
       uni t (_type decl)
       return t

-- |Infer a program in a given context
inferProg :: Context t -> Program t -> Either (TyExcept t) (Context t)
inferProg ctx (Program {_decls = decls}) =
  foldl fun (return ctx) decls
  where
    fun ctx decl@(Decl { _name, _ann, _type, _body }) =
      do ctx0 <- ctx
         t <- inferDecl ctx0 decl
         -- top-level definitions are inherently stable, since they cannot
         -- capture any non-stable values
         return $ extend ctx0 (_name, (t, QStable))

-- |Run an inference computation and solve it
solveInfer :: Context t -> Infer t (Type t) -> Either (TyExcept t) (Scheme t)
solveInfer ctx inf = do
  (ty, fnms, (cs, sts)) <- runInfer ctx inf
  (subst, unies) <- runSolve fnms (un cs)
  case find (not . isStable) $ map unStableTy $ apply subst sts of
    Nothing -> Right (closeOver $ apply subst ty)
    Just notStable -> Left $ TyExcept (NotStableTy notStable, emptyCtx)
  where
    closeOver = normalize . generalize emptyCtx
    un cs = Unifier (nullSubst, cs)


-- |Attempt to unify two types
unifies :: Type t -> Type t -> Solve t (Unifier t)
-- A type unifies to itself with no substitution
unifies t1 t2 | unitFunc t1 == unitFunc t2 = return emptyUnifier
-- Any type unifies to a type-variable by binding the type to the name
unifies (TyVar _ v) t = v `bind` t
unifies t (TyVar _ v) = v `bind` t
-- Two function types unifies their domains and codomains unifies
unifies (TyArr _ t1 t2)  (TyArr _ t3 t4)  = unifyMany [t1,t2] [t3,t4]
unifies (TyProd _ t1 t2) (TyProd _ t3 t4) = unifyMany [t1,t2] [t3,t4]
unifies (TySum _ t1 t2)  (TySum _ t3 t4)  = unifyMany [t1,t2] [t3,t4]
unifies (TyStable _ t1)  (TyStable _ t2)  = t1 `unifies` t2
unifies (TyLater _ t1)   (TyLater _ t2)   = t1 `unifies` t2
unifies (TyStream _ t1)  (TyStream _ t2)  = t1 `unifies` t2
-- Two recursive types unify if their inner types unify after we've replaced
-- the name of the bound type-variable to a fresh name in both types
unifies (TyRec a af t1)  (TyRec _ bf t2)  = do
  fv <- freshName
  apply (M.singleton af (TyVar a fv)) t1 `unifies`
    apply (M.singleton bf (TyVar a fv)) t2
unifies t1 t2 = do
  unif <- getUni
  typeErr (CannotUnify t1 t2 unif) emptyCtx

-- |Unify many types
unifyMany :: [Type t] -> [Type t] -> Solve t (Unifier t)
unifyMany [] [] = return emptyUnifier
unifyMany (t1 : ts1) (t2 : ts2) =
  do Unifier (su1, cs1) <- unifies t1 t2
     Unifier (su2, cs2) <- unifyMany (apply su1 ts1) (apply su1 ts2)
     return $ Unifier (su2 `compose` su1, cs1 ++ cs2)
unifyMany t1 t2 = typeErr (UnificationMismatch t1 t2) emptyCtx

-- |Solves a Solve monad, or fails if there are no solutions
solver :: Solve t (Subst t)
solver = do
  Unifier (su, cs) <- getUni
  case cs of
    [] -> return su
    (Constraint (t1,t2) : cs0) -> do
      Unifier (su1, cs1) <- unifies t1 t2
      putUni $ Unifier (su1 `compose` su, cs1 ++ (apply su1 cs0))
      solver

-- |Put a Unifier
putUni :: MonadState (SolveState t) m => Unifier t -> m ()
putUni u = modify (\(_,n) -> (u,n))

-- |Get a Unifier
getUni :: MonadState (SolveState t) m => m (Unifier t)
getUni = fst <$> get

-- |Record that two types must unify
uni :: Type t -> Type t -> Infer t ()
uni t1 t2 = tell ([Constraint (t1, t2)], [])

-- |Record that a type must be stable
stable :: Type t -> Infer t ()
stable t = tell ([], [StableTy t])

-- |Union two ctxs
unionCtx :: Context t -> Context t -> Context t
unionCtx (Ctx c1) (Ctx c2) = Ctx (c1 `M.union` c2)

-- |Map a function over a context
mapCtx :: (QualSchm t -> QualSchm t) -> Context t -> Context t
mapCtx fn (Ctx m) = Ctx (M.map fn m)

-- |Turn a context into a /later/ context.
-- This effectively steps the context one tick, deleting all
-- /now/ types and changing all /later/ values
-- to /now/
laterCtx :: Context t -> Context t
laterCtx (Ctx c1) =
  Ctx $ M.map (maybe (error "laterCtx") (id)) $ M.filter isJust $ M.map mapper c1 where
    mapper (t,q) = case q of
      QNow    -> Nothing
      QStable -> Just (t, QStable)
      QLater  -> Just (t, QNow)

-- |Turn a context into a /stable/ context.
-- This deletes all types in the context that are not stable
stableCtx :: Context t -> Context t
stableCtx (Ctx c1) =
  Ctx $ M.map (maybe (error "stableCtx") (id)) $ M.filter isJust $ M.map mapper c1 where
    mapper (t,q) = case q of
      QNow    -> Nothing
      QStable -> Just (t, QStable)
      QLater  -> Nothing

-- |Runs an inference action in a context with a schema bound to the given name
inCtx :: (Name, QualSchm t) -> Infer t a -> Infer t a
inCtx (x, sc) m = local scope m where
  scope e = (remove e x) `extend` (x, sc)

-- |Runs an inference action in a stable context with a schema bound to
-- the given name
inStableCtx :: (Name, QualSchm t) -> Infer t a -> Infer t a
inStableCtx (x, sc) m = local scope m where
  scope ctx = (stableCtx . remove ctx $ x) `extend` (x, sc)

-- |Infer a term to be /now/
inferNow :: Term t -> Infer t (Type t)
inferNow expr = do
  t <- infer expr
  return t
  -- ctx <- ask
  -- if (q == QNow || q == QStable)
  --   then return (t,QNow)
  --   else typeErr (NotNow expr) ctx

-- |Infer a term to be /later/
inferLater :: Term t -> Infer t (Type t)
inferLater expr = do
  t <- local laterCtx $ infer expr
  return t
  -- ctx0 <- ask
  -- if (q == QNow)
  --   then return (t,q)
  --   else typeErr (NotLater expr) ctx0

-- |Infer a term to /stable/
inferStable :: Term t -> Infer t (Type t)
inferStable expr = do
  t <- local stableCtx $ infer expr
  return t
  -- if (q == QNow )
  --   then return t
  --   else typeErrM (NotStable expr)

-- |Infer the type of a term.
-- Does not actually return the type, but rather the collection of all
-- type constraints generated by the term, to be solved later.
infer :: Term t -> Infer t (Type t)
infer term = case term of
  TmLit a (LNat _)  -> return (TyPrim a TyNat)
  TmLit a (LBool _) -> return (TyPrim a TyBool)
  TmAlloc a         -> return (TyAlloc a)
  TmPntr a l        -> typeErrM (NotSyntax term)
  TmPntrDeref a l   -> typeErrM (NotSyntax term)

  TmFst a e -> do
    t1 <- inferNow e
    tv1 <- TyVar a <$> freshName
    tv2 <- TyVar a <$> freshName
    uni t1 (TyProd a tv1 tv2)
    return tv1

  TmSnd a e -> do
    t1 <- inferNow e
    tv1 <- TyVar a <$> freshName
    tv2 <- TyVar a <$> freshName
    uni t1 (TyProd a tv1 tv2)
    return tv2

  TmTup a e1 e2 -> do
    t1 <- inferNow e1
    t2 <- inferNow e2
    return (TyProd a t1 t2)

  TmVar a x -> do
    t <- lookupCtx x
    return (t)

  TmLam a x mty e -> do
    tv <- TyVar a <$> freshName
    t <- inCtx (x, (Forall [] tv, QNow)) (inferNow e)
    maybe (return ()) (uni tv) mty -- unify with type ann
    return (TyArr a tv t)

  TmApp a e1 e2 -> do
    t1 <- inferNow e1
    t2 <- inferNow e2
    tv <- TyVar a <$> freshName
    uni t1 (TyArr a t2 tv)
    return tv

  TmLet a p e1 e2 -> do
    t1 <- inferNow e1
    ctx2 <- inferPtn p t1
    local (`unionCtx` ctx2) (inferNow e2)

  TmFix a x mty e -> do
    tv <- TyVar a <$> freshName
    t <- inStableCtx (x, (Forall [] tv, QLater)) (inferNow e)
    uni tv t
    maybe (return ()) (uni tv) mty -- unify with type ann
    return tv

  TmBinOp a op e1 e2 -> do
    t1 <- inferNow e1
    t2 <- inferNow e2
    (ret, left, right) <- binOpTy a op
    uni t1 left
    uni t2 right
    return ret
    -- tv <- TyVar a <$> freshName
    -- let u1 = TyArr a t1 (TyArr a t2 tv)
    -- u2 <- binOpTy a op
    -- uni u1 u2
    -- return tv

  TmITE a cond tr fl -> do
    t1 <- inferNow cond
    t2 <- inferNow tr
    t3 <- inferNow fl
    uni t1 (TyPrim a TyBool)
    uni t2 t3
    return t2

  TmCons a hd tl -> do
    t1 <- inferNow hd
    t2 <- inferNow tl
    tv <- TyVar a <$> freshName
    uni t2 (TyLater a (TyStream a t1))
    uni tv (TyStream a t1)
    return tv

  TmPromote a e -> do
    t1 <- inferNow e
    stable t1
    return (TyStable a t1)

  TmStable a e -> do
    t1 <- inferStable e
    return (TyStable a t1)

  TmDelay a u e -> do
    tu <- inferNow u
    uni tu (TyAlloc a)
    te <- inferLater e
    return (TyLater a te)

  TmInl a e -> do
    ty <- inferNow e
    tvr <- TyVar a <$> freshName
    return (TySum a ty tvr)

  TmInr a e -> do
    ty <- inferNow e
    tvl <- TyVar a <$> freshName
    return (TySum a tvl ty)

  TmCase a e (nm1, c1) (nm2, c2) -> do
    ty <- inferNow e
    tvl <- TyVar a <$> freshName
    tvr <- TyVar a <$> freshName
    uni ty (TySum a tvl tvr)
    t1 <- inCtx (nm1, (Forall [] tvl, QNow)) $ inferNow c1
    t2 <- inCtx (nm2, (Forall [] tvr, QNow)) $ inferNow c2
    uni t1 t2
    return t1

  -- Into must have a type annotation
  TmInto ann tyann e -> do
    case tyann of
      TyRec a alpha tau -> do
        ty <- inferNow e
        let substwith = (TyLater a $ TyRec a alpha tau)
        uni ty (apply (M.singleton alpha substwith) tau)
        return (TyRec a alpha tau)

      _ -> do
        alpha <- freshName
        tau'  <- TyVar ann <$> freshName
        typeErrM (UnificationMismatch [tyann] [TyRec ann alpha tau'])

  -- Out must have a type annotation
  TmOut ann tyann e ->
    case tyann of
      TyRec a alpha tau' -> do
        tau <- inferNow e
        uni tyann tau
        let substwith = (TyLater ann tau)
        let tau'' = apply (M.singleton alpha substwith) tau'
        return (tau'')

      _ -> do
        alpha <- freshName
        tau'  <- TyVar ann <$> freshName
        typeErrM (UnificationMismatch [tyann] [TyRec ann alpha tau'])


  where
    -- infer the type of a binary-operator expression
    -- stupidly returns (resultType, leftType, rightType)
    binOpTy :: a -> BinOp -> Infer a (Type a, Type a, Type a)
    binOpTy a =
      let fromPrim (x,y,z) = (TyPrim a x, TyPrim a y, TyPrim a z)
          -- toArr (x,y,z)    = TyArr a y (TyArr a z x)
          -- primArr = toArr . fromPrim
      in  \case
        --                        ret     left    right
        Add  -> return $ fromPrim (TyNat , TyNat , TyNat )
        Sub  -> return $ fromPrim (TyNat , TyNat , TyNat )
        Mult -> return $ fromPrim (TyNat , TyNat , TyNat )
        Div  -> return $ fromPrim (TyNat , TyNat , TyNat )
        And  -> return $ fromPrim (TyBool, TyBool, TyBool)
        Or   -> return $ fromPrim (TyBool, TyBool, TyBool)
        Leq  -> return $ fromPrim (TyBool, TyNat , TyNat )
        Lt   -> return $ fromPrim (TyBool, TyNat , TyNat )
        Geq  -> return $ fromPrim (TyBool, TyNat , TyNat )
        Gt   -> return $ fromPrim (TyBool, TyNat , TyNat )
        Eq   -> do
          tv <- TyVar a <$> freshName
          return $ (TyPrim a TyBool, tv, tv)
          -- let (|->) = TyArr a
          -- return (tv |-> (tv |-> TyPrim a TyBool))

-- |"Type check" a pattern. Basically, it unfold the pattern, makes sure
-- it matches the term, and then returns a context with all the bound names
-- Lets are not generalized, unfortunately. It works right now, but I'm pretty
-- sure it is not correct. Ask your supervisors!
inferPtn :: Pattern -> Type t -> Infer t (Context t)
inferPtn pattern ty = case pattern of

  PBind nm -> do
    ctx <- ask
    -- generalizing is not so easy with type inference since we cannot
    -- simply get the free variables of a constrained type variable
    -- let sc = generalize ctx ty
    let sc = Forall [] ty
    return . Ctx $ M.singleton nm (sc, QNow)

  PDelay nm -> do
    ctx <- ask
    let ann = typeAnn ty
    fnm <- freshName
    let tv = TyVar ann fnm
    uni ty (TyLater ann tv)
    return $ Ctx $ M.singleton nm (Forall [] tv, QLater)

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

-- |Normalize a type-scheme in the sense that we rename all the
-- type variables to be in alphabetical order of occurence
normalize :: Scheme t -> Scheme t
normalize (Forall _ body) = Forall (map snd ord) (normtype ord body)
  where
    ord = zip (nub $ S.toList $ ftv body) (letters)

    normtype ord ty = case ty of
      TyProd   a l r    -> TyProd a   (normtype ord l) (normtype ord r)
      TySum    a l r    -> TySum a    (normtype ord l) (normtype ord r)
      TyArr    a l r    -> TyArr a    (normtype ord l) (normtype ord r)
      TyLater  a ty     -> TyLater a  (normtype ord ty)
      TyStable a ty     -> TyStable a (normtype ord ty)
      TyStream a ty     -> TyStream a (normtype ord ty)
      TyRec    a nm ty  -> TyRec a nm (normtype ((nm,nm):ord) ty)
      TyAlloc  a        -> ty
      TyPrim{}          -> ty

      TyVar    a name   ->
        case Prelude.lookup name ord of
          Just x  -> TyVar a x
          Nothing -> error $ "type variable " ++ name ++ " not in signature"

