
module FRP.Semantics where

import Data.Map.Strict (Map)
import Data.Map.Strict as M
import Control.Monad.State

-- import FRP.AST

-- type Scope = Map String Term
-- type Store = Map String Term

-- data EvalState = EvalState
--   { _store :: Store
--   , _scope :: Scope
--   }

-- type EvalM a = StateT EvalState Maybe a

-- initialState :: EvalState
-- initialState = EvalState M.empty M.empty

-- getStore :: EvalM Store
-- getStore = _store <$> get

-- getScope :: EvalM Scope
-- getScope = _scope <$> get

-- putVar :: Name -> Term -> EvalM ()
-- putVar x t = do
--   scope <- getScope
--   st <- get
--   let scope' = insert x t scope
--   put $ st { _scope = scope' }

-- localVar :: Name -> Term -> EvalM a -> EvalM a
-- localVar x t eval = do
--   scope <- getScope
--   st <- get
--   let scope' = insert x t scope
--   put $ st { _scope = scope' }
--   r <- eval
--   put st
--   return r


-- evalStep :: Term -> EvalM Term
-- evalStep e = case e of
--   TmFst trm -> do
--     TmTup x y <- evalStep trm
--     return x
--   TmSnd trm -> do
--     TmTup x y <- evalStep trm
--     return y
--   TmTup trm1 trm2 -> TmTup <$> evalStep trm1 <*> evalStep trm2
--   TmInl trm -> TmInl <$> evalStep trm
--   TmInr trm -> TmInr <$> evalStep trm
--   TmCase trm (nml, trml) (nmr, trmr) -> do
--     res <- evalStep trm
--     case res of
--       TmInl vl -> (subst nml `with` vl `inTerm` trml) >>= evalStep
--       TmInr vr -> (subst nmr `with` vr `inTerm` trmr) >>= evalStep
--       _        -> lift Nothing
--   TmLam nm trm -> return $ TmLam nm trm
--   TmApp e1 e2 -> do
--     TmLam x e1' <- evalStep e1
--     v2 <- evalStep e2
--     evalStep =<< (subst x `with` v2 `inTerm` e1')
--   TmCons hd tl -> do
--     hd' <- evalStep hd
--     tl' <- evalStep tl
--     return $ TmCons hd' tl'
--   TmVar nm -> do
--     scope <- getScope
--     lift $ M.lookup nm scope
--   TmLit  l -> return $ TmLit l
--   --TmPntr

-- tmConstInt :: Int -> Term
-- tmConstInt x = TmLam "x" (TmLit (LInt x))

-- runEval :: EvalM a -> EvalState -> Maybe a
-- runEval e = fmap fst . runStateT e

-- runEvalInit :: EvalM a -> Maybe a
-- runEvalInit e = fmap fst . runStateT e $ initialState

-- evalTerm :: Term -> Maybe Term
-- evalTerm = runEvalInit . evalStep

-- -- (subst n x v) replaces all occurences of n with x in the expression v
-- -- but in this implementation it
-- subst :: Name -> Term -> Term -> EvalM Term
-- subst name term term' = localVar name term (return term')

-- -- helper for more readable substitution syntax
-- with :: (Term -> Term -> m Term) -> Term -> (Term -> m Term)
-- with = ($)

-- -- helper for more readable substitution syntax
-- inTerm :: (Term -> m Term) -> Term -> m Term
-- inTerm  = ($)

-- -- subst n `with` x `inTerm` v

-- --subst
-- --   TmVar nm
-- --   TmDelay alloc trm
-- --   TmPromote trm
-- --   TmLet pat trm1 trm2
-- --   TmLit lit
-- --   TmBinOp op l r
-- --   TmITE b trmt trmr
-- --   TmPntr val
-- --   TmPntrDeref val
-- --   TmAlloc