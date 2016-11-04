
module FRP.Semantics where

import Data.Map.Strict (Map)
import Data.Map.Strict as M
import Control.Monad.State

import FRP.AST

type EvalM = StateT Store Maybe Value

type Store = Map String Value

evalStep :: Term -> EvalM
evalStep e = case e of
  TmFst trm -> do
    VTup x y <- evalStep trm
    return x
  TmSnd trm -> do
    VTup x y <- evalStep trm
    return y
  TmTup trm1 trm2 -> VTup <$> evalStep trm1 <*> evalStep trm2
  TmInl trm -> VInl <$> evalStep trm
  TmInr trm -> VInr <$> evalStep trm
  TmCase trm (nml, trml) (nmr, trmr) -> do
    res <- evalStep trm
    case res of
      VInl vl -> evalStep (subst vl nml trml)
      VInr vr -> evalStep (subst vr nmr trmr)
      _       -> lift Nothing
  TmLam nm trm -> return $ VLam nm trm
  TmApp trm1 trm2 -> do
    VLam nm v1 <- evalStep trm1
    v2 <- evalStep trm2
    evalStep (subst v2 nm v1)
  TmCons hd tl -> do
    hd' <- evalStep hd
    tl' <- evalStep tl
    return $ VCons hd' tl'
  TmVar nm -> do
    store <- get
    lift $ M.lookup nm store

runEval :: EvalM -> Store -> Maybe Value
runEval e = fmap fst . runStateT e

subst :: Value -> Name -> Term -> Term
subst = undefined

--subst
--   TmVar nm
--   TmDelay alloc trm
--   TmPromote trm
--   TmLet pat trm1 trm2
--   TmLit lit
--   TmBinOp op l r
--   TmITE b trmt trmr
--   TmPntr val
--   TmPntrDeref val
--   TmAlloc