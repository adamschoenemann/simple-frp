{-# LANGUAGE FlexibleInstances #-}

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
  | SVLater Term Env
  deriving (Show, Eq)

type Scope = Map Name Term
type Store = Map Label StoreVal


instance Pretty StoreVal where
 ppr n = \case
    SVNow v       -> text "->now"   <+> ppr n v
    SVLater e env -> text "->later" <+> ppr n e
                   $$ text ", env" <> parens (ppr n env)

instance Pretty (Map Label StoreVal) where
  ppr n m = vcat . M.elems $ M.mapWithKey mapper m where
    mapper k v = char '{' <> int k <+> ppr n v <> char '}'


data EvalState = EvalState
  { _store    :: Store
  , _labelGen :: Int
  } deriving (Show, Eq)

instance Pretty EvalState where
  ppr n (EvalState {_store = s, _labelGen = lg}) =
    text "labelGen =" <+> int lg
    $$ ppr n s

type EvalM a = StateT EvalState (Reader Env) a

initialState :: EvalState
initialState = EvalState M.empty 0

getStore :: EvalM Store
getStore = _store <$> get

allocVal :: StoreVal -> EvalM Label
allocVal v = do
  label <- genLabel
  --traceM ("allocate " ++ show label ++ " as " ++ ppshow v)
  let change st@(EvalState {_store = s}) =
        let s' = M.insert label v s
        in st {_store = s'}
  modify change
  return label

unsafeLookup :: (Ord k, Show k, Show v) => k -> Map k v -> v
unsafeLookup k m = case M.lookup k m of
  Just x  -> x
  Nothing -> error $ show k ++ " not found in map " ++ show m

lookupPntr :: Label -> EvalM StoreVal
lookupPntr lbl = do
  store <- getStore
  case M.lookup lbl store of
    Nothing -> error $ "pntr " ++ show lbl ++ " not in store " ++ show store
    Just x -> return x

useVar :: String -> EvalM Value
useVar x = do
  env <- ask
  case M.lookup x env of
    Nothing        -> crash $ "var " ++ x ++ " not in env."
    Just (Left  t) -> eval t
    Just (Right v) -> return v


crash :: String -> EvalM a
crash s = do
  env <- ask
  store <- get
  error $ s ++ "\nenv: " ++ ppshow env ++ "\nstore" ++ ppshow store

genLabel :: EvalM Label
genLabel = do
  st <- get
  let gen = _labelGen st
  put $ st { _labelGen = succ gen }
  return gen


evalExpr :: Env -> Term -> Value
evalExpr = evalExpr' initialState

evalExpr' :: EvalState -> Env -> Term -> Value
evalExpr' s env term = fst $ runExpr s env term

runExpr :: EvalState -> Env -> Term -> (Value, EvalState)
runExpr initState initEnv term =
  let (v, s) = runReader (runStateT (eval term) initState) initEnv
  in  -- trace ("runExpr " ++ ppshow term ++ " with lg " ++ show (_labelGen initState) ++ " = " ++ ppshow v) $
      (v,s)

eval :: Term -> EvalM Value
eval term = case term of
  TmVar x -> useVar x
  TmLit x -> return $ VLit x
  TmLam x e -> VClosure x e <$> ask
  TmClosure x t e -> return $ VClosure x t e
  TmApp e1 e2 -> do
    e3 <- eval e1
    case e3 of
      VClosure x e1' env' -> do
        v2 <- eval e2
        let env'' = M.insert x (Right v2) env'
        local (M.union env'') $ eval e1'
      _ -> crash $ "expected closure, got " ++ (ppshow e3)
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
  TmFix x e ->
    local (M.insert x (Left $ TmFix x e)) $ eval e
  TmDelay e' e -> do
    VAlloc <- eval e'
    env' <- ask
    label <- allocVal (SVLater e env')
    return $ VPntr label
  TmPntrDeref label -> do
    v <- lookupPntr label
    case v of
      SVNow v' -> return v'
      -- _             -> return $ VPntr label -- this is debatable if correct
      er       -> crash $ "illegal pntr deref " ++ ppshow (TmPntrDeref label) ++ ".\n" ++ (ppshow er)
  TmStable e ->
    VStable <$> eval e
  TmPromote e ->
    VStable <$> eval e
  TmCase trm (nml, trml) (nmr, trmr) -> do
    res <- eval trm
    case res of
      VInl vl -> local (M.insert nml (Right vl)) $ eval trml
      VInr vr -> local (M.insert nmr (Right vr)) $ eval trmr
      _       -> error "not well-typed"
  TmLet pat e e' -> do
    v <- eval e
    env' <- matchPat pat v
    local (M.union env') $ eval e'
  TmAlloc -> return VAlloc
  TmPntr l -> return $ VPntr l
  TmITE b et ef -> do
    VLit (LBool b') <- eval b
    case b' of
      True  -> eval et
      False -> eval ef
  where
  matchPat :: Pattern -> Value -> EvalM Env
  matchPat (PBind x) v   = return $ M.singleton x (Right v)
  matchPat (PDelay x) (VPntr l) =
    return $ M.singleton x (Left $ TmPntrDeref l)
  matchPat (PStable pat) (VStable v) =
    matchPat pat v
  -- matchPat (PCons (PBind x) (PDelay (PBind y))) (VCons v (VPntr l)) = do
  --   tl <- eval (TmPntrDeref l)
  --   return $ M.fromList [(x,v), (y, tl)]
  matchPat (PCons hdp tlp) (VCons hd tl) =
    M.union <$> matchPat hdp hd <*> matchPat tlp tl
  matchPat pat v = do
    env <- ask
    store <- get
    error $ ppshow pat ++ " cannot match " ++ ppshow v
          ++ "\nenv: " ++ (ppshow env) ++ "\nstore: " ++ ppshow store

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
tick st
  | M.null (_store st) = st
  | otherwise = M.foldlWithKey' tock st (_store st) where
      tock acc k (SVLater e env) =
          let (v, st') =
                  -- trace ("eval " ++ show k ++ "," ++ ppshow e ++ ", env: " ++ ppshow env ++ " in " ++ show acc ++ "\n") $
                  runExpr acc env e
              s = _store st'
          in  st' { _store  = M.insert k (SVNow v) s }
      tock acc k (SVNow _)  = acc { _store = M.delete k (_store acc) }


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
  {-trace (ppshow globals) $-} runExpr initialState globals startMain where
    globals    = globalEnv decls
    startMain = mainTerm (_body main)

runProgram :: Program -> Value
runProgram (Program main decls) = keepRunning initialState startMain
  where
    keepRunning s e  =
      let (p, s') = runExpr s globals e
          s'' = tick s'
      in case p of
        VCons v (VPntr l) -> VCons (deepRunning s'' v) (keepRunning s'' (TmPntrDeref l))
        _                 -> error $ ppshow p ++ " not expected"
    deepRunning s = \case
      VCons x (VPntr l) -> keepRunning s (TmPntrDeref l)
      v                 -> v
    globals    = globalEnv decls
    startMain = mainTerm (_body main)

interpProgram :: Program -> [Value]
interpProgram = toHaskList . runProgram

toHaskList = \case
  VCons h t -> h : toHaskList t
  v         -> error $ "expected cons but got " ++ ppshow v


mainTerm body = TmApp body (TmFix "xs" $ TmCons TmAlloc (TmDelay TmAlloc (TmVar "xs")))
                           --(TmCons TmAlloc $ TmDelay TmAlloc (TmCons TmAlloc $ TmDelay TmAlloc (TmCons TmAlloc TmAlloc)))
globalEnv decls = foldl go M.empty decls where
  go env (Decl t n b) = M.insert n (Right $ evalExpr env b) env