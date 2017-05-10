{-|
Module      : FRP.Semantics
Description : Operational Semantics

This module implements the operational semantics from the paper
-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module FRP.Semantics (
    StoreVal(..)
  , globalEnv
  , Store
  , tick
  , EvalState(..)
  , initialState
  , EvalM
  , toHaskList
  , runExpr
  , evalExpr
  , runTermInEnv
  , stepProgram
  , runProgram
  , interpProgram
  ) where

import           Utils (unsafeLookup)
import           Control.Monad.Reader
import           Control.Monad.State
import           Data.Map.Strict      (Map)
import qualified Data.Map.Strict      as M
import           Debug.Trace
import           Data.List (find)

import           FRP.AST
import           FRP.AST.Construct
import           FRP.Pretty


-- |An item in the store
data StoreVal
  -- |is a value that is available now or
  = SVNow Value
  -- |a term along with an environment that is available later
  | SVLater EvalTerm Env
  deriving (Show, Eq)

instance Pretty StoreVal where
 ppr n = \case
    SVNow v       -> text "->now"   <+> ppr n v
    SVLater e env -> text "->later" <+> ppr n e
                   $$ text ", env" <> parens (ppr n env)

-- |A store is a map from pointer-labels to store values
type Store = Map Label StoreVal

instance Pretty Store where
  ppr n m = vcat . M.elems $ M.mapWithKey mapper m where
    mapper k v = char '{' <> integer k <+> ppr n v <> char '}'

-- |The state for the Eval monad is a store and a counter
-- that generates pointer labels
data EvalState = EvalState
  { _store    :: Store
  , _labelGen :: Integer
  } deriving (Show, Eq)

instance Pretty EvalState where
  ppr n (EvalState {_store = s, _labelGen = lg}) =
    text "labelGen =" <+> integer lg
    $$ ppr n s

-- |The Eval monad handles evaluation of programs
newtype EvalM a = EvalM {unEvalM :: StateT EvalState (Reader Env) a}
  deriving (Functor, Applicative, Monad, MonadState EvalState, MonadReader Env)

-- |the initial state for the evaluator is with an empty Store and
-- a label generator at 0
initialState :: EvalState
initialState = EvalState M.empty 0

-- |Get the store
getStore :: EvalM Store
getStore = _store <$> get

-- |Allocate a value on the store, changing the state
allocVal :: StoreVal -> EvalM Label
allocVal v = do
  label <- genLabel
  modify (alloc label)
  return label
  where
    alloc label st = st { _store = M.insert label v (_store st) }


-- |Lookup a pointer in the store
lookupPntr :: Label -> EvalM StoreVal
lookupPntr lbl = do
  store <- getStore
  case M.lookup lbl store of
    Nothing -> error $ "pntr " ++ show lbl ++ " not in store " ++ show store
    Just x  -> return x

-- |Get a Value from the Env
useVar :: String -> EvalM Value
useVar x = do
  env <- ask
  case M.lookup x env of
    Nothing        -> crash $ "var " ++ x ++ " not in env."
    Just (Left  t) -> eval t
    Just (Right v) -> return v

-- |Crash the evaluator
crash :: String -> EvalM a
crash s = do
  env <- ask
  store <- get
  error $ s ++ "\nenv: " ++ ppshow env ++ "\nstore" ++ ppshow store

-- |Generate a new pointer label, updating the state
genLabel :: EvalM Label
genLabel = do
  st <- get
  let gen = _labelGen st
  put $ st { _labelGen = succ gen }
  return gen

-- |Evaluate an expression in an environment, but with an initial state
evalExpr :: Env -> EvalTerm -> Value
evalExpr = evalExpr' initialState

-- |Evaluate an expression in a given state and environment
evalExpr' :: EvalState -> Env -> EvalTerm -> Value
evalExpr' s env term = fst $ runExpr s env term

-- |Run an expression\/term in a given state and environment
runExpr :: EvalState -> Env -> EvalTerm -> (Value, EvalState)
runExpr initState initEnv term =
  let (v, s) = runReader (runStateT (unEvalM $ eval term) initState) initEnv
  in  -- trace ("runExpr " ++ ppshow term ++ " with lg " ++ show (_labelGen initState) ++ " = " ++ ppshow v) $
      (v,s)

-- |Main evaluation function. This encodes the operational semantics from
-- the paper
eval :: EvalTerm -> EvalM Value
eval term = case term of
  TmVar _a x -> useVar x
  TmLit _a x -> return $ VLit x
  -- eval a lambda to a closure that captures the current scope
  TmLam _a x _ty e -> VClosure x e <$> ask

  TmApp _a e1 e2 -> do
    e3 <- eval e1
    case e3 of
      VClosure x e1' env' -> do
        v2 <- eval e2
        let env'' = M.insert x (Right v2) env'
        local (M.union env'') $ eval e1'
      _ -> crash $ "expected closure, got " ++ (ppshow e3)

  TmBinOp _a op el er -> evalBinOp op el er

  TmFst _a trm -> do
    VTup x y <- eval trm
    return x

  TmSnd _a trm -> do
    VTup x y <- eval trm
    return y

  TmTup _a trm1 trm2 -> VTup <$> eval trm1 <*> eval trm2
  TmInl _a trm       -> VInl <$> eval trm
  TmInr _a trm       -> VInr <$> eval trm
  TmCons _a hd tl    -> VCons <$> eval hd <*> eval tl
  TmFix _a x ty e    -> local (M.insert x (Left $ term)) $ eval e

  -- delay a term by allocating it on the store
  TmDelay _a e' e -> do
    v <- eval e'
    case v of
      VAlloc -> do
        env' <- ask
        label <- allocVal (SVLater e env')
        return $ VPntr label
      _ -> crash $ "expected VAlloc, got" ++ (ppshow v)

  -- dereference a pointer
  TmPntrDeref _a label -> do
    v <- lookupPntr label
    case v of
      SVNow v' -> return v'
      er       -> crash $ "illegal pntr deref " ++ ppshow (tmpntrderef label) ++ ".\n" ++ (ppshow er)

  TmStable _a e -> VStable <$> eval e
  TmPromote _a e -> VStable <$> eval e

  TmCase _a trm (nml, trml) (nmr, trmr) -> do
    res <- eval trm
    case res of
      VInl vl -> local (M.insert nml (Right vl)) $ eval trml
      VInr vr -> local (M.insert nmr (Right vr)) $ eval trmr
      _       -> crash "not well-typed"

  -- eval a let by binding the name to the scope using 'matchPat'
  TmLet _a pat e e' -> do
    v <- eval e
    env' <- matchPat pat v
    local (M.union env') $ eval e'

  TmAlloc _a -> return VAlloc
  TmPntr _a l -> return $ VPntr l

  TmITE _a b et ef -> do
    VLit (LBool b') <- eval b
    case b' of
      True  -> eval et
      False -> eval ef

  TmOut _a _ty e -> do
    VInto v <- eval e
    return v

  TmInto _a _ty e -> do
    v <- eval e
    return $ VInto v

  where
    -- evaluate a pattern match
    matchPat :: Pattern -> Value -> EvalM Env
    matchPat (PBind x) v   = return $ M.singleton x (Right v)
    matchPat (PDelay x) (VPntr l) =
      return $ M.singleton x (Left $ tmpntrderef l)
    matchPat (PStable pat) (VStable v) =
      matchPat pat v
    matchPat (PCons hdp tlp) (VCons hd tl) =
      M.union <$> matchPat hdp hd <*> matchPat tlp tl
    matchPat (PTup p1 p2) (VTup v1 v2) =
      M.union <$> matchPat p1 v1 <*> matchPat p2 v2
    matchPat pat v = do
      env <- ask
      store <- get
      error $ ppshow pat ++ " cannot match " ++ ppshow v
            ++ "\nenv: " ++ (ppshow env) ++ "\nstore: " ++ ppshow store

    -- evaluate a binary operator
    evalBinOp op el er = case op of
        Add  -> intOp    (+)
        Sub  -> intOp    (-)
        Mult -> intOp    (*)
        Div  -> intOp    div
        And  -> boolOp   (&&)
        Or   -> boolOp   (||)
        Leq  -> intCmpOp (<=)
        Lt   -> intCmpOp (<)
        Geq  -> intCmpOp (>=)
        Gt   -> intCmpOp (>)
        Eq   -> eqOp
        where
          intOp fn = do
            VLit (LNat x)  <- eval el
            VLit (LNat y)  <- eval er
            return $ VLit (LNat $ fn x y)
          boolOp fn = do
            VLit (LBool x) <- eval el
            VLit (LBool y) <- eval er
            return $ VLit (LBool $ fn x y)
          intCmpOp fn = do
            VLit (LNat x)  <- eval el
            VLit (LNat y)  <- eval er
            return $ VLit (LBool $ fn x y)
          eqOp = do
            VLit x <- eval el
            VLit y <- eval er
            return $ VLit (LBool (x == y))


-- |Tick a store.
--
-- All now values are deleted
-- all later terms are promoted to now by eval'ing it in the
-- so-far-ticked store.
-- There is an implicit ordering imposed here, so we evaluate the
-- pointers from smallest-to-biggest since allocated values can
-- only depend on other allocations with a pointer label that is
-- smaller than their own.
tick :: EvalState -> EvalState
tick st
  | M.null (_store st) = st
  | otherwise = M.foldlWithKey' tock st (_store st) where
      tock acc k (SVLater e env) =
          let (v, st') = runExpr acc env e
              s = _store st'
          in  st' { _store  = M.insert k (SVNow v) s }
      tock acc k (SVNow _)  = acc { _store = M.delete k (_store acc) }

-- |Evaluate a program one step.
stepProgram :: Program a -> (Value, EvalState)
stepProgram (Program {_decls = decls}) =
  let main = maybe (error "no main function") id
           $ find (\d -> _name d == "main") decls
  in  case main of
    Decl _a _ty _nm body -> runExpr initialState globals (mainEvalTerm $ unitFunc body)
  where
    globals    = globalEnv decls

-- |Run a term in an environment
runTermInEnv :: Env -> Term () -> Value
runTermInEnv env trm =
  keepRunning initialState trm
  where
    keepRunning s e  =
      let (p, s') = runExpr s env e
          s'' = tick s'
      in case p of
        VCons v (VPntr l) -> VCons (deepRunning s'' v) (keepRunning s'' (tmpntrderef l))
        _                 -> error $ ppshow p ++ " not expected"

    deepRunning s = \case
      VCons x (VPntr l) -> keepRunning s (tmpntrderef l)
      v                 -> v

-- |Run a program
runProgram :: Program a -> Value
runProgram (Program {_decls = decls}) = runTermInEnv globals startMain
  where
    main = maybe (error "no main function") id
           $ find (\d -> _name d == "main") decls

    globals   = globalEnv decls

    startMain = case main of
      Decl _a _ty _nm body -> mainEvalTerm $ unitFunc body

-- |Run a program and convert the result to a haskell list of
-- values.
interpProgram :: Program a -> [Value]
interpProgram = toHaskList . runProgram

-- |Convert a Value (which is hopefully a Cons) to a Haskell list
toHaskList :: Value -> [Value]
toHaskList = \case
  VCons h t -> h : toHaskList t
  v         -> error $ "expected cons but got " ++ ppshow v

-- |Wrap a function in an application with a fixpoint of allocators.
-- This will produce a term that is ready to be evaluated, assuming
-- it is given a "main" function of type @forall a. S alloc -> S a$
mainEvalTerm :: EvalTerm -> EvalTerm
mainEvalTerm body = tmapp body (tmfix "xs" undefined $ tmcons tmalloc (tmdelay tmalloc (tmvar "xs")))

-- |Take a list of declarations and convert into a \"global\" environment
globalEnv :: [Decl a] -> Env
globalEnv decls = foldl go M.empty decls
  where
    go env (Decl _a t n b) = M.insert n (Right $ evalExpr env $ unitFunc b) env
