
module FRP.Semantics where

import           Control.Monad.Reader
import           Control.Monad.State
import           Data.Map.Strict      (Map)
import qualified Data.Map.Strict      as M
import           Debug.Trace

import           FRP.AST
import           FRP.Pretty

data Qualifier
  = QNow
  | QStable
  | QLater
  deriving (Show)

data StoreVal
  = SVNow Value
  | SVLater Term
  | SVNull
  deriving (Show)

type Scope = Map Name Term
type Store = Map Label StoreVal

data EvalState = EvalState
  { _store    :: Store
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
  Just x  -> x
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

type Env = Map String Value

evalExpr :: Env -> Term -> Value
evalExpr = evalExpr' initialState

evalExpr' :: EvalState -> Env -> Term -> Value
evalExpr' s env term = fst $ runExpr s env term

runExpr :: EvalState -> Env -> Term -> (Value, EvalState)
runExpr s env term = runReader (runStateT (eval term) s) env where
  eval :: Term -> EvalM Value
  eval term = case term of
    TmVar x -> unsafeLookup x <$> ask
    TmLit x -> return $ VLit x
    TmLam x e -> VClosure x e <$> ask
    TmClosure x t e -> return $ VClosure x t e
    TmApp e1 e2 -> do
      e3 <- eval e1
      case e3 of
        VClosure x e1' env' -> do
          v2 <- eval e2
          let env'' = M.insert x v2 env'
          local (const env'') $ eval e1'
        _ -> error $ "expected closure, got " ++ (ppshow e3)
    TmBinOp op el er -> evalBinOp op el er
    TmFst trm -> do
      VTup x y <- eval trm
      return x
    TmSnd trm -> do
      VTup x y <- eval trm
      return y
    TmTup trm1 trm2 -> VTup <$> eval trm1 <*> eval trm2
    TmInl trm -> VInl <$> eval trm
    TmInr trm -> VInr <$> eval trm
    TmCons hd tl -> VCons <$> eval hd <*> eval tl
    TmFix x e -> eval (z `TmApp` (TmLam x e)) -- use Z combinator for strict fixedpoint
      where
        zinner =
            (TmLam "x"
              (TmVar "f" `TmApp`
                (TmLam "y" (TmVar "x" `TmApp` TmVar "x" `TmApp` TmVar "y"))
              ))
        z = TmLam "f" (zinner `TmApp` zinner)
      -- Z = λf. (λx. f (λy. x x y))(λx. f (λy. x x y))
    TmDelay e' e -> do
      VAlloc <- eval e'
      label <- allocVal (SVLater e)
      return $ VPntr label
    TmPntrDeref label -> do -- really, is this that is meant?
      v <- lookupPntr label
      case v of
        SVNow v' -> return v'
        _        -> return $ VPntr label -- this is debatable if correct
        -- er       -> error $ "expected SVNow but got " ++ (show er)
    TmStable e ->
      VStable <$> eval e
    TmPromote e ->
      VStable <$> eval e
    TmCase trm (nml, trml) (nmr, trmr) -> do
      res <- eval trm
      case res of
        VInl vl -> local (M.insert nml vl) $ eval trml
        VInr vr -> local (M.insert nmr vr) $ eval trmr
        _       -> error "not well-typed"
    TmLet pat e e' -> do
      v <- eval e
      env <- matchPat pat v
      local (M.union env) $ eval e'
    TmAlloc -> return VAlloc
    TmPntr l -> return $ VPntr l
    TmITE b et ef -> do
      VLit (LBool b') <- eval b
      case b' of
        True  -> eval et
        False -> eval ef

  matchPat :: Pattern -> Value -> EvalM Env
  matchPat (PBind x) v   = return $ M.singleton x v
  matchPat (PDelay pat) (VPntr l) = do
    v <- eval (TmPntrDeref l)
    matchPat pat v
  matchPat (PStable pat) (VStable v) =
    matchPat pat v
  matchPat (PCons hdp tlp) (VCons hd tl) =
    M.union <$> matchPat hdp hd <*> matchPat tlp tl
  matchPat pat v = error $ ppshow pat ++ " cannot match " ++ ppshow v

  evalPat :: Pattern -> Term -> Term -> EvalM Value
  evalPat (PBind x) e e' = do
    v <- eval e
    local (M.insert x v) $ eval e'
  evalPat (PDelay pat) e e' = do
    v <- eval e
    case v of
      VPntr l -> evalPat pat (TmPntrDeref l) e'
      er      -> error $ "expected pntr but got " ++ ppshow er
  evalPat (PStable pat) e e' = do
    VStable v <- eval e
    evalPat pat (valToTerm v) e'
  -- evalPat (PCons (PBind x) (PDelay (PBind xs))) e e' = do
  --   VCons hd tl <- eval e
  --   local (M.insert x hd . M.insert xs tl) $ eval e'
  evalPat (PCons hdp tlp) e e' = do
    VCons hd tl <- eval e
    evalPat hdp (valToTerm hd) (TmLet tlp (valToTerm tl) e')
  -- evalPat pat _ _ =
  --   error $ "unexpected pattern " ++ show pat ++ ". This should not typecheck"

  evalBinOp op el er = case op of
      Add  -> intOp (+)
      Sub  -> intOp (-)
      Mult -> intOp (*)
      Div  -> intOp div
      And  -> boolOp (&&)
      Or   -> boolOp (||)
      Leq  -> intCmpOp (<=)
      Lt   -> intCmpOp (<)
      Geq  -> intCmpOp (>=)
      Gt   -> intCmpOp (>)
      Eq   -> eqOp
      where
        intOp fn = do
          VLit (LInt x) <- eval el
          VLit (LInt y) <- eval er
          return $ VLit (LInt $ fn x y)
        boolOp fn = do
          VLit (LBool x) <- eval el
          VLit (LBool y) <- eval er
          return $ VLit (LBool $ fn x y)
        intCmpOp fn = do
          VLit (LInt x) <- eval el
          VLit (LInt y) <- eval er
          return $ VLit (LBool $ fn x y)
        eqOp = do
          VLit x <- eval el
          VLit y <- eval er
          return $ VLit (LBool (x == y))


tick :: EvalState -> EvalState
tick st@(EvalState {_store = s})
  | M.null s = st
  | otherwise = st {_store = M.map tock s'} where
      s'  = M.filter isNow s
      st' = st {_store = s'}
      tock (SVLater e) = SVNow (evalExpr' st' M.empty e)
      tock _           = error "Only later vals should be in store"
      isNow (SVNow _) = True
      isNow _         = False

tmConstInt :: Int -> Term
tmConstInt x = TmLam "x" (TmLit (LInt x))

-- make name point to term in term
-- subst :: Name -> Term -> Term -> EvalM Term
-- subst = local


-- actual good old-fashioned substituion
subst' :: Name -> Term -> Term -> Term
subst' name nterm term' = go term' where
  go term'' = case term'' of
    TmVar x                            | x == name -> nterm
    TmVar x                            -> term''
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
    TmFix x e                          -> TmFix x (go e)


-- helper for more readable substitution syntax
with' :: (Term -> Term -> Term) -> Term -> (Term -> Term)
with' = ($)

-- helper for more readable substitution syntax
inTerm' :: (Term -> Term) -> Term -> Term
inTerm'  = ($)

evalProgram :: Program -> (Value, EvalState)
evalProgram (Program main decls) =
  runExpr initialState env startMain where
    env    =
      foldl (\env (Decl t n b) -> M.insert n (evalExpr env b) env) M.empty decls
    mainBody = _body main
    -- allocs   = TmFix "ds" (TmCons TmAlloc (TmDelay TmAlloc (TmVar "ds")))
    startMain = TmApp mainBody (TmCons TmAlloc $ TmDelay TmAlloc TmAlloc)

runProgram :: Program -> [Value]
runProgram (Program main decls) = keepRunning startMain initialState
  where
    keepRunning e s =
      let (p, s') = runExpr s globals e
      in case p of
        VCons v (VPntr l) -> v : keepRunning (TmPntrDeref l) (tick s)
        _                 -> error $ ppshow p ++ " not expected"
    globals    =
      foldl (\env (Decl t n b) -> M.insert n (evalExpr env b) env) M.empty decls
    mainBody = _body main
    -- allocs   = TmFix "ds" (TmCons TmAlloc (TmDelay TmAlloc (TmVar "ds")))
    startMain = TmApp mainBody (TmCons TmAlloc $ TmDelay TmAlloc TmAlloc)
