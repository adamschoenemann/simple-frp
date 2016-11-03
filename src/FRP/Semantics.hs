
module FRP.Semantics where

import Data.Map.Strict
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
      _       -> undefined

subst :: Value -> Name -> Term -> Term
subst = undefined
--subst

--   TmLam nm trm
--   TmVar nm
--   TmApp trm1 trm2
--   TmCons hd tl
--   TmDelay alloc trm
--   TmPromote trm
--   TmLet pat trm1 trm2
--   TmLit lit
--   TmBinOp op l r
--   TmITE b trmt trmr
--   TmPntr val
--   TmPntrDeref val
--   TmAlloc