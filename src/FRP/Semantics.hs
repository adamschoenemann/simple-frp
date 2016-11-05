
module FRP.Semantics where

import Data.Map.Strict (Map)
import Data.Map.Strict as M
import Control.Monad.State
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
  , _scope :: Scope
  , _labelGen :: Int
  } deriving (Show)


type EvalM a = State EvalState a

initialState :: EvalState
initialState = EvalState M.empty M.empty 0

getStore :: EvalM Store
getStore = _store <$> get

getScope :: EvalM Scope
getScope = _scope <$> get

putVar :: Name -> Term -> EvalM ()
putVar x t = do
  scope <- getScope
  st <- get
  let scope' = insert x t scope
  put $ st { _scope = scope' }

local :: s -> State s a -> State s a
local x comp = do
  y <- get
  put x
  z <- comp
  put y
  return z

-- this is very hard to implement for some reason
-- or is it even here the error lies?
localVar :: Name -> Term -> EvalM a -> EvalM a
localVar x t eval = do
  st <- get
  let scope' = insert x t $ _scope st
  local (st { _scope = scope' }) eval

  -- scope <- getScope
  -- st <- get
  -- let scope' = insert x t scope
  -- let st' = st { _scope = scope' }
  -- let (r, st'') = runEval eval st'
  -- return r

  -- st <- get
  -- let scope = _scope st
  -- let scope' = insert x t $ scope
  -- put $ st { _scope = scope' }
  -- r <- eval
  -- -- st' <- get
  -- -- put $ st' { _scope = scope }
  -- return r



allocVal :: StoreVal -> EvalM Label
allocVal v = do
  store <- getStore
  label <- genLabel
  let store' = M.insert label v store
  st <- get
  put $ st { _store = store' }
  return label

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

evalStep :: Term -> EvalM Term
evalStep e = do
  s <- get
  traceM (show $ _scope s)
  evalStep' e

evalStep' e = case e of
  TmFst trm -> do
    TmTup x y <- evalStep trm
    return x
  TmSnd trm -> do
    TmTup x y <- evalStep trm
    return y
  TmTup trm1 trm2 -> TmTup <$> evalStep trm1 <*> evalStep trm2
  TmInl trm -> TmInl <$> evalStep trm
  TmInr trm -> TmInr <$> evalStep trm
  TmCase trm (nml, trml) (nmr, trmr) -> do
    res <- evalStep trm
    case res of
      TmInl vl -> (subst nml `with` vl `inTerm` trml)
      TmInr vr -> (subst nmr `with` vr `inTerm` trmr)
      _        -> error "not well-typed"
  TmLam nm trm -> return $ TmLam nm trm
  TmApp e1 e2 -> do
    -- traceM ("apply " ++ ppshow e1 ++ " to " ++ ppshow e2)
    TmLam x e1' <- evalStep e1
    v2 <- evalStep e2
    st <- get
    let scope = _scope st
    modify (\s ->
                let scope = _scope s
                    scope' = insert x v2 scope
                in  s {_scope = scope'}
           )
    r <- evalStep e1'
    st' <- get
    put $ st' { _scope = scope }
    return r

    -- (subst x `with` v2 `inTerm` e1')
  TmCons hd tl -> do
    hd' <- evalStep hd
    tl' <- evalStep tl
    return $ TmCons hd' tl'
  TmVar nm -> do
    scope <- getScope
    return $ unsafeLookup nm scope
  TmLit  l -> return $ TmLit l
  TmDelay e' e -> do
    TmAlloc <- evalStep e'
    label <- allocVal (SVal e QLater)
    return $ TmPntr label
  TmPntrDeref label -> do
    (SVal v QNow) <- lookupPntr label
    return v
  TmStable e ->
    TmStable <$> evalStep e
  TmPromote e ->
    TmStable <$> evalStep e
  TmLet pat e e' -> case pat of
    PBind x -> subst x `with` e `inTerm` e'
    PDelay (PBind x) -> do
      TmPntr lbl <- evalStep e
      subst x `with` (TmPntrDeref lbl) `inTerm` e'
    PStable (PBind x) -> do
      TmStable v <- evalStep e
      (subst x `with` v `inTerm` e')
    PCons (PBind x) (PDelay (PBind xs)) -> do
      TmCons v (TmPntr l) <- evalStep e
      e'' <- subst x `with` v `inTerm` e'
      subst xs `with` (TmPntr l) `inTerm` e''
    _ -> error $ "unexpected pattern " ++ show pat ++ ". This should not typecheck"
  TmAlloc -> return TmAlloc
  TmPntr l -> return $ TmPntr l
  TmITE b et ef -> do
    TmLit (LBool b') <- evalStep b
    case b' of
      True -> evalStep et
      False -> evalStep ef
  TmBinOp op el er -> case op of
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
        TmLit (LInt x) <- evalStep el
        TmLit (LInt y) <- evalStep er
        return $ TmLit (LInt $ fn x y)
      boolOp fn = do
        TmLit (LBool x) <- evalStep el
        TmLit (LBool y) <- evalStep er
        return $ TmLit (LBool $ fn x y)
      intCmpOp fn = do
        TmLit (LInt x) <- evalStep el
        TmLit (LInt y) <- evalStep er
        return $ TmLit (LBool $ fn x y)
      eqOp = do
        TmLit x <- evalStep el
        TmLit y <- evalStep er
        return $ TmLit (LBool (x == y))

tmConstInt :: Int -> Term
tmConstInt x = TmLam "x" (TmLit (LInt x))

runEval :: EvalM a -> EvalState -> (a, EvalState)
runEval e = runState e

runEvalInit :: EvalM a -> (a, EvalState)
runEvalInit e = runEval e $ initialState

evalTerm :: Term -> Term
evalTerm = fst . runEvalInit . evalStep

-- (subst n x v) replaces all occurences of n with x in the expression v
-- but in this implementation it just assigns the variable
-- to the local scope
subst :: Name -> Term -> Term -> EvalM Term
subst name term term' =
  trace ("substituting " ++ name ++ " with " ++ (ppshow term) ++ " in " ++ ppshow term')
    localVar name term (evalStep term')

-- helper for more readable substitution syntax
with :: (Term -> Term -> m Term) -> Term -> (Term -> m Term)
with = ($)

-- helper for more readable substitution syntax
inTerm :: (Term -> m Term) -> Term -> m Term
inTerm  = ($)

execProgramStep :: Program -> EvalState -> Term
execProgramStep (Program main decls) state =
  fst $ runEval (evalStep $ startMain) state where
    mainBody = _body main
    startMain = TmApp mainBody (TmCons TmAlloc TmAlloc)