
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

tmout :: EvalTerm -> EvalTerm
tmout = TmOut ()

tminto :: EvalTerm -> EvalTerm
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

tmint  = tmlit . LInt
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

tmfix :: Name -> EvalTerm -> EvalTerm
tmfix = TmFix ()

infixr 0 -->
(-->) :: Name -> EvalTerm -> EvalTerm
(-->) = tmlam

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

typaram = TyParam ()
typrod = TyProd ()
tysum = TySum ()
tyarr = TyArr ()
tylater = TyLater ()
tystable = TyStable ()
tystream = TyStream ()
tyalloc = TyAlloc ()
tynat = TyNat ()
tybool = TyBool ()

(.*.) :: Type () -> Type () -> Type ()
(.*.) = TyProd ()

infixr 0 |->
(|->) :: Type () -> Type () -> Type ()
(|->) = TyArr ()
