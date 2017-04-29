{-|
Module      : FRP.AST.Construct
Description : Helper functions to construct ASTs by hand
-}
module FRP.AST.Construct where

import           FRP.AST

tmfst :: EvalTerm -> EvalTerm
tmfst = TmFst ()

tmsnd :: EvalTerm -> EvalTerm
tmsnd = TmSnd ()

tmtup :: EvalTerm -> EvalTerm -> EvalTerm
tmtup = TmTup ()

tminl :: EvalTerm -> EvalTerm
tminl = TmInl ()

tminr :: EvalTerm -> EvalTerm
tminr = TmInr ()

tmcase :: EvalTerm -> (Name, EvalTerm) -> (Name, EvalTerm) -> EvalTerm
tmcase = TmCase ()

tmlam :: Name -> EvalTerm -> EvalTerm
tmlam n t = TmLam () n Nothing t

tmlamty :: Name -> Type () -> EvalTerm -> EvalTerm
tmlamty n ty t = TmLam () n (Just ty) t

tmvar :: Name -> EvalTerm
tmvar = TmVar ()

tmapp :: EvalTerm -> EvalTerm -> EvalTerm
tmapp = TmApp ()

tmcons :: EvalTerm -> EvalTerm -> EvalTerm
tmcons = TmCons ()

tmout :: Type () -> EvalTerm -> EvalTerm
tmout = TmOut ()

tminto :: Type () -> EvalTerm -> EvalTerm
tminto = TmInto ()


tmstable :: EvalTerm -> EvalTerm
tmstable = TmStable ()

tmdelay :: EvalTerm -> EvalTerm -> EvalTerm
tmdelay = TmDelay ()

tmpromote :: EvalTerm -> EvalTerm
tmpromote = TmPromote ()

tmlet :: Pattern -> EvalTerm -> EvalTerm -> EvalTerm
tmlet = TmLet ()

tmlit :: Lit -> EvalTerm
tmlit = TmLit ()

tmint  = tmlit . LNat
tmbool = tmlit . LBool

tmbinop :: BinOp -> EvalTerm -> EvalTerm -> EvalTerm
tmbinop = TmBinOp ()

tmite :: EvalTerm -> EvalTerm -> EvalTerm -> EvalTerm
tmite = TmITE ()

tmpntr :: Label -> EvalTerm
tmpntr = TmPntr ()

tmpntrderef :: Label -> EvalTerm
tmpntrderef = TmPntrDeref ()

tmalloc :: EvalTerm
tmalloc = TmAlloc ()

tmfix :: Name -> Type () -> EvalTerm -> EvalTerm
tmfix n ty t = TmFix () n (Just ty) t

infixr 0 -->
(-->) :: Name -> EvalTerm -> EvalTerm
(-->) = tmlam

infixr 0 -:>
(-:>) :: (Name, Type ()) -> EvalTerm -> EvalTerm
(nm, ty) -:> trm = tmlamty nm ty trm

infixl 9 <|
(<|) :: EvalTerm -> EvalTerm -> EvalTerm
(<|) = tmapp

eq :: EvalTerm -> EvalTerm -> EvalTerm
eq = tmbinop Eq

(<==) :: EvalTerm -> EvalTerm -> EvalTerm
(<==) = tmbinop Leq

(>==) :: EvalTerm -> EvalTerm -> EvalTerm
(>==) = tmbinop Geq

(>.) :: EvalTerm -> EvalTerm -> EvalTerm
(>.) = tmbinop Gt

(<.) :: EvalTerm -> EvalTerm -> EvalTerm
(<.) = tmbinop Lt

tyvar = TyVar ()
typrod = TyProd ()
tysum = TySum ()
tyarr = TyArr ()
tylater = TyLater ()
tystable = TyStable ()
tystream = TyStream ()
tyrec = TyRec ()
tyalloc = TyAlloc ()
tynat  = TyPrim () TyNat
tybool = TyPrim () TyBool

(.*.) :: Type () -> Type () -> Type ()
(.*.) = TyProd ()

(.+.) :: Type () -> Type () -> Type ()
(.+.) = TySum ()

infixr 1 |->
(|->) :: Type () -> Type () -> Type ()
(|->) = TyArr ()
