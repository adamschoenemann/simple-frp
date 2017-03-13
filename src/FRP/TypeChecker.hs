{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveFunctor #-}

module FRP.TypeChecker where

import           Control.Monad.Except
import           Control.Monad.State
import           FRP.Pretty
import           Data.Map.Strict                (Map)
import qualified Data.Map.Strict                as M
import           FRP.AST
import           FRP.AST.Construct (tmvar)
import           Debug.Trace
import           Data.Maybe (isJust)


type Ty t = (Type t, Qualifier)
newtype Context t = Ctx {unCtx :: Map Name (Ty t)} deriving (Show, Eq)

instance Pretty (Context t) where
  ppr n (Ctx map) = vcat $ fmap mapper $ M.toList map where
    mapper (k, v) = text k <+> char ':' <+> ppr 0 v

newtype TypeErr t = TypeErr (Err t, Context t)
  deriving (Show, Eq)

data Err t
  = CannotUnify (Ty t) (Ty t) (Term t)
  | OccursCheckFailed Name (Ty t)
  | UnknownIdentifier Name
  | NotSyntax (Term t)
  | TypeAnnRequired (Term t)
  | NotStableTy (Ty t)
  | NotStableVar Name
  | NotNow (Term t)
  deriving (Show, Eq)

instance Pretty (TypeErr t) where
  ppr n (TypeErr (err, ctx)) = ppr n err $$ text "in context: " $$ ppr n ctx

instance Pretty (Err t) where
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



newtype CheckM t a = CheckM (ExceptT (TypeErr t) (State [Name]) a)
  deriving ( Functor, Applicative, Monad, MonadState [Name]
           , MonadError (TypeErr t))


freshName :: CheckM t Name
freshName = do
  nm:nms <- get
  put nms
  return nm

typeErr :: Err t -> Context t -> CheckM t a
typeErr err ctx = throwError (TypeErr (err, ctx))

lookupCtx :: Name -> Context t -> Maybe (Ty t)
lookupCtx nm (Ctx m) = M.lookup nm m

getVar :: Context t -> Name -> CheckM t (Ty t)
getVar (Ctx m) nm = case M.lookup nm m of
  Nothing -> typeErr (UnknownIdentifier nm) (Ctx m)
  Just x  -> return x

extendCtx :: Name -> Ty t -> Context t -> Context t
extendCtx n t c = Ctx $ M.insert n t $ unCtx c

unionCtx :: Context t -> Context t -> Context t
unionCtx (Ctx c1) (Ctx c2) = Ctx (c1 `M.union` c2)

-- my stack image does not have traversMaybeWithKey :/
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


isStable :: Type t -> Bool
isStable (TyNat _)      = True
isStable (TyBool _)     = True
isStable (TyProd _ a b) = isStable a && isStable b
isStable (TySum  _ a b) = isStable a && isStable b
isStable (TyStable _ _) = True
isStable _              = False

emptyCtx :: Context t
emptyCtx = Ctx M.empty

runCheckTerm ctx t = runCheckM (checkTerm ctx t)
runCheckTerm' t = runCheckM (checkTerm emptyCtx t)

runCheckM :: CheckM t a -> Either (TypeErr t) a
runCheckM (CheckM m) = evalState (runExceptT m) (infiniteSupply alphabet)
  where
    alphabet = map (:[]) ['a'..'z']
    infiniteSupply supply = supply ++ addSuffixes supply (1 :: Integer)
    addSuffixes xs n = (map (\x -> addSuffix x n) xs) ++ (addSuffixes xs (n+1))
    addSuffix x n = x ++ show n

-- I dunno, this is not really doing what I want.
-- I want to avoid the "UnkownIdentifier" err for a variable that has been
-- removed by laterCtx or stableCtx
-- think about it some more...
pushCtxHandler :: forall t. Context t -> CheckM t (Ty t) -> CheckM t (Ty t)
pushCtxHandler ctx m = m `catchError` handler where
  handler :: TypeErr t -> CheckM t (Ty t)
  handler (TypeErr (e@(UnknownIdentifier nm), ctx')) =
      case lookupCtx nm ctx of
        Nothing -> typeErr e ctx
        Just _  -> typeErr (NotStableVar nm) ctx
  handler e = throwError e

checkTerm :: Context t -> Term t -> CheckM t (Ty t)
checkTerm ctx term = case term of
  TmFst a trm -> checkTerm ctx trm >>= \case
    (TyProd _ t1 t2, QNow) -> return (t1, QNow)
    (ty, q) ->
        typeErr (CannotUnify
                  (TyProd a (TyParam a "a0") (TyParam a "a1"), QNow)
                  (ty, q)
                  term
                ) ctx
  TmSnd a trm -> checkTerm ctx trm >>= \case
    (TyProd _ t1 t2, QNow) -> return (t2, QNow)
    (ty, q) ->
        typeErr (CannotUnify
                  (TyProd a (TyParam a "a0") (TyParam a "a1"), QNow)
                  (ty, q)
                  term
                ) ctx
  TmTup a trm1 trm2      -> do
    (t1, QNow) <- checkTerm ctx trm1
    (t2, QNow) <- checkTerm ctx trm2
    return $ (TyProd a t1 t2, QNow)
  TmInl a trm            -> do
    (t1, QNow) <- checkTerm ctx trm
    b <- freshName
    return $ (TySum a t1 (TyParam a b), QNow)
  TmInr a trm            -> do
    (t2, QNow) <- checkTerm ctx trm
    b <- freshName
    return $ (TySum a (TyParam a b) t2, QNow)
  TmCase a trm (vl, trml) (vr, trmr) -> do
    (TySum a' t1 t2, QNow) <- checkTerm ctx trm
    (c1, QNow) <- checkTerm (extendCtx vl (t1, QNow) ctx) trml
    (c2, QNow) <- checkTerm (extendCtx vr (t2, QNow) ctx) trmr
    if (unitFunc c1 /= unitFunc c2)
      then typeErr (CannotUnify (c1, QNow) (c2, QNow) term) ctx
      else return (c1, QNow)
  TmLam a nm mty trm ->
    case mty of
      Nothing -> typeErr (TypeAnnRequired term) ctx
      Just ty -> do
        (bdty, QNow) <- checkTerm (extendCtx nm (ty, QNow) ctx) trm
        return (TyArr a ty bdty, QNow)
  -- below will not work without explicit type annotations
  TmFix a x ty0 trm          ->
    case ty0 of
      Nothing -> typeErr (TypeAnnRequired term) ctx
      Just ty -> do
        let ctx2 = extendCtx x (ty, QLater) $ laterCtx ctx
        typeAnnotated <- inferFixLamTy ctx ty trm
        (ty1, q) <- checkTerm ctx2 typeAnnotated
        if ((unitFunc ty, QNow) /= (unitFunc ty1, QNow))
          then typeErr (CannotUnify (ty, QNow) (ty1, q) term) ctx
          else return (ty, QNow)
  TmVar a v              -> do
    (vt, q) <- getVar ctx v
    if q `elem` [QNow, QStable]
     then return (vt, QNow)
     else typeErr (CannotUnify (vt, q) (vt, QNow) term) ctx
  TmApp a trm1 trm2      -> do
    (TyArr _ at bt, QNow) <- checkTerm ctx trm1
    (t2, QNow) <- checkTerm ctx trm2
    if (unitFunc t2 == unitFunc at)
      then return (bt, QNow)
      else typeErr (CannotUnify (t2, QNow) (at, QNow) term) ctx
  TmCons a hd tl         -> do
    hty <- checkTerm ctx hd
    tlty <- checkTerm ctx tl
    case hty of
      (ht, QNow) -> do
        tlty <- checkTerm ctx tl
        case tlty of
          (TyLater _ (TyStream tla tlt), QNow) -> return (TyStream a tlt, QNow)
          _ -> typeErr (CannotUnify
                            (TyLater a (TyStream a ht), QNow)
                            tlty
                            term
                        ) ctx
      (ht, q)    -> typeErr (CannotUnify (ht, q) (ht, QNow) term) ctx
  TmDelay a alloc trm    -> do
    (TyAlloc _, QNow) <- checkTerm ctx alloc
    (t, q)  <- checkTerm (laterCtx ctx) trm
    return (TyLater a t, QNow)
  TmStable a trm         -> do
    (t, QNow) <- checkTerm (stableCtx ctx) trm
    return (TyStable a t, QNow)
  TmPromote a trm        -> do
    (ty, QNow) <- checkTerm ctx trm
    if isStable ty
      then return (TyStable a ty, QNow)
      else checkTerm (stableCtx ctx) trm >>= \case
        (t, QNow) -> return (TyStable a t, QNow)
        (t, q)    -> typeErr (NotStableTy (t, q)) ctx
  TmLet a ptn trm1 trm2   -> do
    t <- checkTerm ctx trm1
    ctx2 <- checkPtn ctx ptn t
    checkTerm ctx2 trm2
  TmLit a l              -> case l of
    LInt  _ -> return (TyNat a, QNow)
    LBool _ -> return (TyBool a, QNow)
  TmBinOp a op l r       -> do
    let (retty, lty, rty) = binOpTy a op
    (lt, QNow) <- checkTerm ctx l
    (rt, QNow) <- checkTerm ctx r
    if unitFunc lt /= unitFunc lty
      then typeErr (CannotUnify (lt, QNow) (lty, QNow) term) ctx
    else if unitFunc rt /= unitFunc rty
      then typeErr (CannotUnify (rt, QNow) (rty, QNow) term) ctx
    else return (retty, QNow)
  TmITE a b trmt trmf    -> do
    (TyBool _, qb) <- checkTerm ctx b
    (tt, qt) <- checkTerm ctx trmt
    (ft, qf) <- checkTerm ctx trmf
    if unitFunc tt == unitFunc ft
      then return (tt, qt)
      else typeErr (CannotUnify (tt, qt) (ft, qf) term) ctx
  TmPntr a p        -> typeErr (NotSyntax term) ctx
  TmPntrDeref a p   -> typeErr (NotSyntax term) ctx
  TmAlloc a              -> return (TyAlloc a, QNow)
  TmOut a trm            -> error "type-checking for TmOut not implemented"
  TmInto a trm           -> error "type-checking for TmInto not implemented"
  where
    binOpTy :: a -> BinOp -> (Type a, Type a, Type a)
    binOpTy a = \case
      Add  -> (TyNat  a, TyNat  a, TyNat  a)
      Sub  -> (TyNat  a, TyNat  a, TyNat  a)
      Mult -> (TyNat  a, TyNat  a, TyNat  a)
      Div  -> (TyNat  a, TyNat  a, TyNat  a)
      And  -> (TyBool a, TyBool a, TyBool a)
      Or   -> (TyBool a, TyBool a, TyBool a)
      Leq  -> (TyBool a, TyNat  a, TyNat  a)
      Lt   -> (TyBool a, TyNat  a, TyNat  a)
      Geq  -> (TyBool a, TyNat  a, TyNat  a)
      Gt   -> (TyBool a, TyNat  a, TyNat  a)
      Eq   -> (TyBool a, TyNat  a, TyNat  a) -- FIXME: this should be parametric

-- dirty hack to avoid duplicate type signatures for fixpoints, e.g.
-- fix (f: Nat -> @(S Nat) -> S Nat). \(x : Nat) (xs : @(S Nat)) -> cons(x, xs)
-- becomes
-- fix (f: Nat -> @(S Nat) -> S Nat). \x xs -> cons(x, xs)
inferFixLamTy :: Context t -> Type t -> Term t -> CheckM t (Term t)
inferFixLamTy ctx (TyArr _ a b) term@(TmLam ann x lty body) =
  let continue = TmLam ann x (Just a) <$> inferFixLamTy ctx b body
  in  case lty of
    Nothing -> continue
    Just lty0 -> if (unitFunc a == unitFunc lty0)
                   then continue
                   else typeErr (CannotUnify (a, QStable) (lty0, QStable) term) ctx
inferFixLamTy ctx ty term = return term

checkPtn :: Context t -> Pattern -> Ty t -> CheckM t (Context t)
checkPtn ctx = go where
  go (PBind nm) t                    = return (extendCtx nm t ctx)
  go (PDelay nm) (TyLater a t, QNow) = return (extendCtx nm (t, QLater) ctx)
  go (PCons hd tl) (TyStream a x, QNow) = do
    ctx1 <- checkPtn ctx hd (x, QNow)
    ctx2 <- checkPtn ctx1 tl (TyLater a (TyStream a x), QNow)
    return ctx2
  go (PStable p) (TyStable a t, QNow) = do
    ctx1 <- checkPtn ctx p (t, QStable)
    return ctx1
  go (PTup p1 p2) (TyProd a t1 t2, QNow) = do
    ctx1 <- checkPtn ctx  p1 (t1, QNow)
    ctx2 <- checkPtn ctx1 p2 (t2, QNow)
    return ctx2
  go p t = typeErr (CannotUnify undefined undefined undefined) ctx

-- to check a declaration, we must first inline the
-- declaration's type with its outermost lambdas
-- We should extend the context with something similar to the rule
-- for fix... Hmmm....
checkDecl :: Context t -> Decl t -> CheckM t (Ty t)
checkDecl ctx (Decl a type0 name bd) = do
  bd0         <- inlineTypes type0 bd
  (type1, q)  <- checkTerm (extendCtx name (type0, QLater) (stableCtx ctx)) bd0
  if (q /= QNow)
    then typeErr (NotNow (TmVar a name)) ctx
  else if (unitFunc type0 /= unitFunc type1)
    then typeErr (CannotUnify (type0, QNow) (type1, q) (TmVar a name)) ctx
  else return (type1, q)

inlineTypes :: Type a -> Term a -> CheckM a (Term a)
inlineTypes t                 term@(TmFix a2 nm t2 bd) =
  case t2 of
    Nothing -> return $ TmFix a2 nm (Just t) bd
    Just _  -> return term
inlineTypes (TyArr _a1 t1 t2) term@(TmLam a2 nm t3 bd) =
  case t3 of
    Nothing -> do
      bd0 <- inlineTypes t2 bd
      return $ TmLam a2 nm (Just t1) bd0
    Just t4 -> if (unitFunc t1 == unitFunc t4)
                 then TmLam a2 nm (Just t4) <$> inlineTypes t2 bd
                 else typeErr (CannotUnify (t1, QNow) (t4, QNow) term) undefined
inlineTypes ty trm = return trm

runCheckDecl ctx t = runCheckM (checkDecl ctx t)
runCheckDecl' t = runCheckM (checkDecl emptyCtx t)


-- specialize type variables (dirty hack for now)
specialize :: Map Name (Type a) -> Type a -> Type a
specialize subst = go where
  go ty = case ty of
    TyParam  _ nm -> maybe ty id $ M.lookup nm subst
    TyProd   a t1 t2 -> TyProd   a (go t1) (go t2)
    TySum    a t1 t2 -> TySum    a (go t1) (go t2)
    TyArr    a t1 t2 -> TyArr    a (go t1) (go t2)
    TyLater  a t     -> TyLater  a (go t)
    TyStable a t     -> TyStable a (go t)
    TyStream a t     -> TyStream a (go t)
    TyAlloc  a       -> TyAlloc  a
    TyNat    a       -> TyNat    a
    TyBool   a       -> TyBool   a