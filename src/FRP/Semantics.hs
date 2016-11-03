
module FRP.Semantics where

import Data.Map.Strict

import FRP.AST

type Store = Map String Value

-- evalStep :: (Store, trm) -> Maybe (Store, Value)
-- evalStep (sig, e) = case e of
--   TmFst trm -> let (sig', e') = evalStep
--   TmSnd trm
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