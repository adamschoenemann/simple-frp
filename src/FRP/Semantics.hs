
module FRP.Semantics where

import Data.Map.Strict (Map)
import Data.Map.Strict as M
import Control.Monad.State
import Control.Monad.Reader
import Debug.Trace

import FRP.AST
import FRP.Pretty

data Qualifier
  = QNow
  | QStable
  | QLater
  deriving (Show)

data StoreVal
  = SVal Term Qualifier
  deriving (Show)

type Scope = Map Name Term
type Store = Map Label StoreVal

data EvalState = EvalState
  { _store :: Store
  , _labelGen :: Int
  } deriving (Show)


type EvalM a = StateT EvalState (Reader Env) a

initialState :: EvalState
initialState = EvalState M.empty 0

getStore :: EvalM Store
getStore = _store <$> get


allocVal :: StoreVal -> EvalM Label
allocVal v = do
  store <- getStore
  label <- genLabel
  let store' = M.insert label v store
  st <- get
  put $ st { _store = store' }
  return label

unsafeLookup :: (Ord k, Show k) => k -> Map k v -> v
unsafeLookup k m = case M.lookup k m of
  Just x -> x
  Nothing -> error $ show k ++ " not found in map"

lookupPntr :: Label -> EvalM StoreVal
lookupPntr lbl = do
  store <- getStore
  return $ unsafeLookup lbl store

genLabel :: EvalM Label
genLabel = do
  st <- get
  let gen = _labelGen st
  put $ st { _labelGen = succ gen }
  return gen

type Env = Map String Term

evalExpr :: Env -> Term -> Term
evalExpr env term = fst $ runReader (runStateT (eval term) initialState) env where
  eval :: Term -> EvalM Term
  eval term = case term of
    TmVar x -> (unsafeLookup x <$> ask)
    TmLit x -> return $ TmLit x
    TmLam x e -> TmClosure x e <$> ask
    TmClosure x t e -> return $ TmClosure x t e
    TmApp e1 e2 -> do
      TmClosure x e1' env' <- eval e1
      v2 <- eval e2
      -- lbl <- show <$> genLabel
      let env'' = {-M.insert x (TmVar lbl) $ -}M.insert x v2 env'
      local (const env'') $ eval e1'
    TmBinOp op el er -> evalBinOp op el er
    TmFst trm -> do
      TmTup x y <- eval trm
      return x
    TmSnd trm -> do
      TmTup x y <- eval trm
      return y
    TmTup trm1 trm2 -> TmTup <$> eval trm1 <*> eval trm2
    TmInl trm -> TmInl <$> eval trm
    TmInr trm -> TmInr <$> eval trm
    TmCons hd tl -> TmCons <$> eval hd <*> eval tl
    TmDelay e' e -> do
      TmAlloc <- eval e'
      label <- allocVal (SVal e QLater)
      return $ TmPntr label
    TmPntrDeref label -> do
      (SVal v QNow) <- lookupPntr label
      return v
    TmStable e ->
      TmStable <$> eval e
    TmPromote e ->
      TmStable <$> eval e
    TmCase trm (nml, trml) (nmr, trmr) -> do
      res <- eval trm
      case res of
        TmInl vl -> local (M.insert nml vl) $ eval trml
        TmInr vr -> local (M.insert nmr vr) $ eval trmr
        _        -> error "not well-typed"
    TmLet pat e e' -> case pat of
      PBind x -> local (M.insert x e) $ eval e'
      PDelay (PBind x) -> do
        TmPntr lbl <- eval e
        local (M.insert x (TmPntrDeref lbl)) $ eval e'
      PStable (PBind x) -> do
        TmStable v <- eval e
        local (M.insert x v) $ eval e'
      PCons (PBind x) (PDelay (PBind xs)) -> do
        TmCons v (TmPntr l) <- eval e
        e'' <- local (M.insert x v) $ eval e'
        local (M.insert xs (TmPntr l)) $ eval e''
      _ -> error $ "unexpected pattern " ++ show pat ++ ". This should not typecheck"
    TmAlloc -> return TmAlloc
    TmPntr l -> return $ TmPntr l
    TmITE b et ef -> do
      TmLit (LBool b') <- eval b
      case b' of
        True -> eval et
        False -> eval ef

  evalBinOp op el er = case op of
      Add -> intOp (+)
      Sub -> intOp (-)
      Mult -> intOp (*)
      Div -> intOp div
      And -> boolOp (&&)
      Or -> boolOp (||)
      Leq -> intCmpOp (<=)
      Lt -> intCmpOp (<)
      Geq -> intCmpOp (>=)
      Gt -> intCmpOp (>)
      Eq -> eqOp
      where
        intOp fn = do
          TmLit (LInt x) <- eval el
          TmLit (LInt y) <- eval er
          return $ TmLit (LInt $ fn x y)
        boolOp fn = do
          TmLit (LBool x) <- eval el
          TmLit (LBool y) <- eval er
          return $ TmLit (LBool $ fn x y)
        intCmpOp fn = do
          TmLit (LInt x) <- eval el
          TmLit (LInt y) <- eval er
          return $ TmLit (LBool $ fn x y)
        eqOp = do
          TmLit x <- eval el
          TmLit y <- eval er
          return $ TmLit (LBool (x == y))

-- eval' e = case e of
--
--   TmBinOp op el er -> case op of
--     Add -> intOp (+)
--     Sub -> intOp (-)
--     Mult -> intOp (*)
--     Div -> intOp div
--     And -> boolOp (&&)
--     Or -> boolOp (||)
--     Leq -> intCmpOp (<=)
--     Lt -> intCmpOp (<)
--     Geq -> intCmpOp (>=)
--     Gt -> intCmpOp (>)
--     Eq -> eqOp
--     where
--       intOp fn = do
--         TmLit (LInt x) <- eval el
--         TmLit (LInt y) <- eval er
--         return $ TmLit (LInt $ fn x y)
--       boolOp fn = do
--         TmLit (LBool x) <- eval el
--         TmLit (LBool y) <- eval er
--         return $ TmLit (LBool $ fn x y)
--       intCmpOp fn = do
--         TmLit (LInt x) <- eval el
--         TmLit (LInt y) <- eval er
--         return $ TmLit (LBool $ fn x y)
--       eqOp = do
--         TmLit x <- eval el
--         TmLit y <- eval er
--         return $ TmLit (LBool (x == y))

tmConstInt :: Int -> Term
tmConstInt x = TmLam "x" (TmLit (LInt x))

-- make name point to term in term
-- subst :: Name -> Term -> Term -> EvalM Term
-- subst = local


-- actual good old-fashioned substituion
subst' :: Name -> Term -> Term -> Term
subst' name nterm term' = go term' where
  go term'' = case term'' of
    TmVar x | x == name -> nterm
    TmVar x -> term''
    TmFst trm                          -> TmFst $ go trm
    TmSnd trm                          -> TmFst $ go trm
    TmTup trm1 trm2                    -> TmTup (go trm1) (go trm2)
    TmInl trm                          -> TmInl $ go trm
    TmInr trm                          -> TmInr $ go trm
    TmCase trm (nml, trml) (nmr, trmr) -> undefined
    TmClosure x trm env                -> TmClosure x (go trm) env
    TmLam nm trm                       -> TmLam nm (go trm)
    TmApp trm1 trm2                    -> TmApp (go trm1) (go trm2)
    TmCons trm1 trm2                   -> TmCons (go trm1) (go trm2)
    TmStable trm                       -> TmStable (go trm)
    TmDelay trm1 trm2                  -> TmDelay (go trm1) (go trm2)
    TmPromote trm                      -> TmPromote (go trm)
    TmLet pat trm1 trm2                -> TmLet pat (go trm1) (go trm2)
    TmLit l                            -> TmLit l
    TmBinOp op trm1 trm2               -> TmBinOp op (go trm1) (go trm2)
    TmITE trm1 trm2 trm3               -> TmITE (go trm1) (go trm2) (go trm3)
    TmPntr lbl                         -> TmPntr lbl
    TmPntrDeref lbl                    -> TmPntrDeref lbl
    TmAlloc                            -> TmAlloc


-- helper for more readable substitution syntax
with' :: (Term -> Term -> Term) -> Term -> (Term -> Term)
with' = ($)

-- helper for more readable substitution syntax
inTerm' :: (Term -> Term) -> Term -> Term
inTerm'  = ($)

execProgram :: Program -> EvalState -> Term
execProgram (Program main decls) state =
  evalExpr M.empty startMain where
    mainBody = _body main
    startMain = TmApp mainBody (TmCons TmAlloc TmAlloc)