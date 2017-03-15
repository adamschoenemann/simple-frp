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


type QualTy t = (Type t, Qualifier)
newtype Context t = Ctx {unCtx :: Map Name (QualTy t)} deriving (Show, Eq)

instance Pretty (Context t) where
  ppr n (Ctx map) = vcat $ fmap mapper $ M.toList map where
    mapper (k, v) = text k <+> char ':' <+> ppr 0 v

newtype TyExcept t = TyExcept (TyErr t, Context t)
  deriving (Show, Eq)

data TyErr t
  = CannotUnify (QualTy t) (QualTy t) (Term t)
  | OccursCheckFailed Name (QualTy t)
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



newtype CheckM t a = CheckM (ExceptT (TyExcept t) (State [Name]) a)
  deriving ( Functor, Applicative, Monad, MonadState [Name]
           , MonadError (TyExcept t))


freshName :: CheckM t Name
freshName = do
  nm:nms <- get
  put nms
  return nm

typeErr :: TyErr t -> Context t -> CheckM t a
typeErr err ctx = throwError (TyExcept (err, ctx))

lookupCtx :: Name -> Context t -> Maybe (QualTy t)
lookupCtx nm (Ctx m) = M.lookup nm m

getVar :: Context t -> Name -> CheckM t (QualTy t)
getVar (Ctx m) nm = case M.lookup nm m of
  Nothing -> typeErr (UnknownIdentifier nm) (Ctx m)
  Just x  -> return x

extendCtx :: Name -> QualTy t -> Context t -> Context t
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
isStable (TyPrim _ _ )  = True
isStable (TyProd _ a b) = isStable a && isStable b
isStable (TySum  _ a b) = isStable a && isStable b
isStable (TyStable _ _) = True
isStable _              = False

emptyCtx :: Context t
emptyCtx = Ctx M.empty

runCheckTerm ctx t = runCheckM (checkTerm ctx t)
runCheckTerm' t = runCheckM (checkTerm emptyCtx t)

runCheckM :: CheckM t a -> Either (TyExcept t) a
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
pushCtxHandler :: forall t. Context t -> CheckM t (QualTy t) -> CheckM t (QualTy t)
pushCtxHandler ctx m = m `catchError` handler where
  handler :: TyExcept t -> CheckM t (QualTy t)
  handler (TyExcept (e@(UnknownIdentifier nm), ctx')) =
      case lookupCtx nm ctx of
        Nothing -> typeErr e ctx
        Just _  -> typeErr (NotStableVar nm) ctx
  handler e = throwError e

checkTerm :: Context t -> Term t -> CheckM t (QualTy t)
checkTerm ctx term = case term of
  TmFst a trm -> checkTerm ctx trm >>= \case
    (TyProd _ t1 t2, QNow) -> return (t1, QNow)
    (ty, q) ->
        typeErr (CannotUnify
                  (TyProd a (TyVar a "a0") (TyVar a "a1"), QNow)
                  (ty, q)
                  term
                ) ctx
  TmSnd a trm -> checkTerm ctx trm >>= \case
    (TyProd _ t1 t2, QNow) -> return (t2, QNow)
    (ty, q) ->
        typeErr (CannotUnify
                  (TyProd a (TyVar a "a0") (TyVar a "a1"), QNow)
                  (ty, q)
                  term
                ) ctx
  TmTup a trm1 trm2 -> do
    (t1, q1) <- checkTerm ctx trm1
    (t2, q2) <- checkTerm ctx trm2
    case (q1,q2) of
      (QNow, QNow) -> return $ (TyProd a t1 t2, QNow)
      (_ ,_)       -> let (eq,et,etrm) = if q1 /= QNow
                                            then (q1, t1,trm1)
                                            else (q2, t2,trm2)
                      in typeErr (CannotUnify (et, QNow) (et, eq) etrm) ctx
  -- these also won't work without explicit type annotations
  TmInl a trm -> checkTerm ctx trm >>= \case
    (t1, QNow) -> freshName >>= (\b -> return (TySum a t1 (TyVar a b), QNow))
    (t1, q)    -> typeErr (CannotUnify (t1, QNow) (t1, q) trm) ctx
  TmInr a trm -> checkTerm ctx term >>= \case
    (t2, QNow) -> freshName >>= (\b -> return (TySum a (TyVar a b) t2, QNow))
    (t2, q)    -> typeErr (CannotUnify (t2, QNow) (t2, q) trm) ctx
  TmCase a trm (vl, trml) (vr, trmr) -> checkTerm ctx term >>= \case
    (TySum a' t1 t2, QNow) -> do
      let lctx = extendCtx vl (t1, QNow) ctx
      let rctx = extendCtx vr (t2, QNow) ctx
      (c1, q1) <- checkTerm lctx trml
      (c2, q2) <- checkTerm rctx trmr
      if (unitFunc c1 /= unitFunc c2)
        then typeErr (CannotUnify (c1, QNow) (c2, QNow) term) ctx
      else if q1 /= QNow
        then typeErr (CannotUnify (c1, QNow) (c1, q1) trml) lctx
      else if q2 /= QNow
        then typeErr (CannotUnify (c2, QNow) (c2, q2) trmr) rctx
      else return (c1, QNow)
    (et, eq) ->
      let expTy = TySum a (TyVar a "a0") (TyVar a "a1")
      in  typeErr (CannotUnify (et, eq) (expTy, QNow) term) ctx
  TmLam a nm mty trm ->
    case mty of
      Nothing -> typeErr (TypeAnnRequired term) ctx
      Just ty -> do
        let bdctx = extendCtx nm (ty, QNow) ctx
        (bdty, q) <- checkTerm bdctx trm
        if (q /= QNow)
          then typeErr (CannotUnify (bdty, QNow) (bdty, q) trm) bdctx
          else return (TyArr a ty bdty, QNow)
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
  TmApp a trm1 trm2      -> checkTerm ctx trm1 >>= \case
    (TyArr _ at bt, QNow) -> do
      (t2, q) <- checkTerm ctx trm2
      if (q /= QNow)
        then typeErr (CannotUnify (t2,QNow) (t2, q) trm2) ctx
      else if (unitFunc t2 /= unitFunc at)
        then typeErr (CannotUnify (t2, QNow) (at, QNow) term) ctx
      else return (bt, QNow)
    (et, eq) -> do
      a1 <- freshName
      a2 <- freshName
      let expTy = TyArr a (TyVar a a1) (TyVar a a2)
      typeErr (CannotUnify (expTy, QNow) (et, eq) trm1) ctx
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
    LInt  _ -> return (TyPrim a TyNat,  QNow)
    LBool _ -> return (TyPrim a TyBool, QNow)
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
    (TyPrim _ TyBool, qb) <- checkTerm ctx b
    (tt, qt) <- checkTerm ctx trmt
    (ft, qf) <- checkTerm ctx trmf
    if unitFunc tt == unitFunc ft
      then return (tt, qt)
      else typeErr (CannotUnify (tt, qt) (ft, qf) term) ctx
  TmPntr a p      -> typeErr (NotSyntax term) ctx
  TmPntrDeref a p -> typeErr (NotSyntax term) ctx
  TmAlloc a       -> return (TyAlloc a, QNow)
  TmOut a trm     -> error "type-checking for TmOut not implemented"
  TmInto a trm    -> error "type-checking for TmInto not implemented"
  where
    binOpTy :: a -> BinOp -> (Type a, Type a, Type a)
    binOpTy a =
      let fromPrim (x,y,z) = (TyPrim a x, TyPrim a y, TyPrim a z)
      in  \case
        Add  -> fromPrim (TyNat , TyNat , TyNat )
        Sub  -> fromPrim (TyNat , TyNat , TyNat )
        Mult -> fromPrim (TyNat , TyNat , TyNat )
        Div  -> fromPrim (TyNat , TyNat , TyNat )
        And  -> fromPrim (TyBool, TyBool, TyBool)
        Or   -> fromPrim (TyBool, TyBool, TyBool)
        Leq  -> fromPrim (TyBool, TyNat , TyNat )
        Lt   -> fromPrim (TyBool, TyNat , TyNat )
        Geq  -> fromPrim (TyBool, TyNat , TyNat )
        Gt   -> fromPrim (TyBool, TyNat , TyNat )
        Eq   -> fromPrim (TyBool, TyNat , TyNat ) -- FIXME:his shoulde parametc

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

-- "Type check" a pattern. Basically, it unfold the pattern, makes sure
-- it matches the term, and then adds the appropriate names to the input context
checkPtn :: Context t -> Pattern -> QualTy t -> CheckM t (Context t)
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
  go p t = typeErr (CannotUnify undefined undefined undefined) ctx -- FIXME

-- check a declaration
-- recursive decls will fail if they've not been written or have been
-- automatically translated to fixpoints after parsing
checkDecl :: Context t -> Decl t -> CheckM t (QualTy t)
checkDecl ctx (Decl a type0 name bd) = do
  bd0         <- inlineTypes type0 bd
  (type1, q)  <- checkTerm ctx bd0
  if (q /= QNow)
    then typeErr (NotNow (TmVar a name)) ctx
  else if (unitFunc type0 /= unitFunc type1)
    then typeErr (CannotUnify (type0, QNow) (type1, q) (TmVar a name)) ctx
  else return (type1, q)

-- inline the type of a declaration into its term, if the term is a lambda
-- or fixpoint
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
                 else typeErr (CannotUnify (t1, QNow) (t4, QNow) term) undefined -- FIXME
inlineTypes ty trm = return trm

runCheckDecl ctx t = runCheckM (checkDecl ctx t)
runCheckDecl' t = runCheckM (checkDecl emptyCtx t)


-- specialize type variables (dirty hack for now)
specialize :: Map Name (Type a) -> Type a -> Type a
specialize subst = go where
  go ty = case ty of
    TyVar  _ nm -> maybe ty id $ M.lookup nm subst
    TyProd   a t1 t2 -> TyProd   a (go t1) (go t2)
    TySum    a t1 t2 -> TySum    a (go t1) (go t2)
    TyArr    a t1 t2 -> TyArr    a (go t1) (go t2)
    TyLater  a t     -> TyLater  a (go t)
    TyStable a t     -> TyStable a (go t)
    TyStream a t     -> TyStream a (go t)
    TyAlloc  a       -> TyAlloc  a
    TyPrim   a p     -> TyPrim a p
