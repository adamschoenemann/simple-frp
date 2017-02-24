{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}

module FRP.TypeChecker where

import           Control.Monad.Except
import           Control.Monad.State
import           Data.Map                   (Map)
import qualified Data.Map                   as M
import           FRP.AST

type Ty t = (Type t, Qualifier)
newtype Context t = Ctx {unCtx :: Map Name (Ty t)}

data TypeErr t
  = CannotUnify (Ty t) (Ty t)
  | OccursCheckFailed Name (Ty t)
  | UnknownIdentifier Name
  | NotStable (Ty t)
  deriving (Show)

newtype CheckM t a = CheckM (ExceptT (TypeErr t) (State [Name]) a)
  deriving ( Functor, Applicative, Monad, MonadState [Name]
           , MonadError (TypeErr t))

freshName :: CheckM t Name
freshName = do
  nm:nms <- get
  put nms
  return nm

getVar :: Context t -> Name -> CheckM t (Ty t)
getVar (Ctx m) nm = case M.lookup nm m of
  Nothing -> throwError (UnknownIdentifier nm)
  Just x  -> return x

extendCtx :: Name -> Ty t -> Context t -> Context t
extendCtx n t c = Ctx $ M.insert n t $ unCtx c

unionCtx :: Context t -> Context t -> Context t
unionCtx (Ctx c1) (Ctx c2) = Ctx (c1 `M.union` c2)

isStable :: Type t -> Bool
isStable (TyNat _)   = True
isStable _           = False

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

checkTerm :: Context t -> Term t -> CheckM t (Ty t)
checkTerm ctx = \case
  TmFst a trm            -> do
    (TyProd _ t1 t2, QNow) <- checkTerm ctx trm
    return (t1, QNow)
  TmSnd a trm            -> do
    (TyProd _ t1 t2, QNow) <- checkTerm ctx trm
    return (t2, QNow)
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
      then throwError (CannotUnify (c1, QNow) (c2, QNow))
      else return (c1, QNow)
  TmLam a nm trm         -> do
    anm <- freshName
    checkTerm (extendCtx nm (TyParam a anm, QNow) ctx) trm
  TmFix a b trm          -> undefined
  TmVar a v              -> do
    (vt, q) <- getVar ctx v
    if q `elem` [QNow, QStable]
     then return (vt, QNow)
     else throwError (CannotUnify (vt, q) (vt, QNow))
  TmApp a trm1 trm2      -> do
    (TyArr _ at bt, QNow) <- checkTerm ctx trm1
    (t2, QNow) <- checkTerm ctx trm2
    if (unitFunc t2 == unitFunc at)
      then return (bt, QNow)
      else throwError (CannotUnify (t2, QNow) (at, QNow))
  TmCons a hd tl         -> do
    (ht, QNow) <- checkTerm ctx hd
    (TyLater _ (TyStream tla tlt), QNow) <- checkTerm ctx tl
    return (TyStream a tlt, QNow)
  TmDelay a alloc trm    -> do
    (t, QLater) <- checkTerm ctx trm
    (TyAlloc _, QNow) <- checkTerm ctx alloc
    return (TyLater a t, QNow)
  TmStable a trm         -> do
    (t, QStable) <- checkTerm ctx trm
    return (TyStable a t, QNow)
  TmPromote a trm        -> do
    (t, QNow) <- checkTerm ctx trm
    if (isStable t)
      then return (TyStable a t, QNow)
      else throwError (NotStable (t, QNow))
  TmLet a ptn trm1 trm2   -> do
    t <- checkTerm ctx trm2
    ctx2 <- checkPtn ctx ptn t
    checkTerm ctx2 trm2
  TmLit a l              -> case l of
    LInt  _ -> return (TyNat a, QNow)
    LBool _ -> return (TyBool a, QNow)
  TmBinOp a op l r       -> undefined
  TmITE a b trmt trmf    -> undefined
  TmPntr a pntr          -> undefined
  TmPntrDeref a pntr     -> undefined
  TmAlloc a              -> undefined
  TmOut a trm            -> undefined
  TmInto a trm           -> undefined

checkPtn :: Context t -> Pattern -> Ty t -> CheckM t (Context t)
checkPtn ctx = go where
  go (PBind nm) t                    = return (extendCtx nm t ctx)
  go (PDelay nm) (TyLater a t, QNow) = return (extendCtx nm (t, QLater) ctx)
  go (PCons hd tl) (TyStream a x, QNow) = do
    ctx1 <- checkPtn ctx hd (x, QNow)
    ctx2 <- checkPtn ctx1 tl (TyLater a (TyStream a x), QNow)
    return ctx2
  go (PStable p) (TyStable a t, QNow) = do
    ctx1 <- checkPtn ctx p (t, QNow)
    return ctx1
  go (PTup p1 p2) (TyProd a t1 t2, QNow) = do
    ctx1 <- checkPtn ctx  p1 (t1, QNow)
    ctx2 <- checkPtn ctx1 p2 (t2, QNow)
    return ctx2
  go p t = throwError (CannotUnify undefined undefined)



-- checkPtn ctx pattern term = case pattern of
--   PBind nm      -> do
--     (t,q) <- checkTerm ctx term
--     return (extendCtx nm (t,q) ctx)
--   PCons p1 p2   -> do
--     t1 <- checkTerm ctx
--   PDelay p1     -> undefined
--   PStable p1    -> undefined
--   PTup p1 p2    -> undefined
