
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
--   TmTup trm1 trm2
--   TmInl trm
--   TmInr trm
--   TmCase trm (nml, trml) (nmr, trmr)
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