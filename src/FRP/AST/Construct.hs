
module FRP.AST.Construct where

import FRP.AST

tmfst :: Term -> Term
tmfst = TmFst

tmsnd :: Term -> Term
tmsnd = TmSnd

tmtup :: Term -> Term -> Term
tmtup = TmTup

tminl :: Term -> Term
tminl = TmInl

tminr :: Term -> Term
tminr = TmInr

tmcase :: Term -> (Name, Term) -> (Name, Term) -> Term
tmcase = TmCase

tmlam :: Name -> Term -> Term
tmlam = TmLam

tmvar :: Name -> Term
tmvar = TmVar

tmapp :: Term -> Term -> Term
tmapp = TmApp

tmcons :: Term -> Term -> Term
tmcons = TmCons

tmout :: Term -> Term
tmout = TmOut

tminto :: Term -> Term
tminto = TmInto

tmclosure :: Name -> Term -> Env -> Term
tmclosure = TmClosure

tmstable :: Term -> Term
tmstable = TmStable

tmdelay :: Term -> Term -> Term
tmdelay = TmDelay

tmpromote :: Term -> Term
tmpromote = TmPromote

tmlet :: Pattern -> Term -> Term -> Term
tmlet = TmLet

tmlit :: Lit -> Term
tmlit = TmLit

tmbinop :: BinOp -> Term -> Term -> Term
tmbinop = TmBinOp

tmite :: Term -> Term -> Term -> Term
tmite = TmITE

tmpntr :: Label -> Term
tmpntr = TmPntr

tmpntrderef :: Label -> Term
tmpntrderef = TmPntrDeref

tmalloc :: Term
tmalloc = TmAlloc

tmfix :: Name -> Term -> Term
tmfix = TmFix

infixr 0 -->
(-->) :: Name -> Term -> Term
(-->) = tmlam

infixl 9 <|
(<|) :: Term -> Term -> Term
(<|) = tmapp

(===) :: Term -> Term -> Term
(===) = tmbinop Eq

(<==) :: Term -> Term -> Term
(<==) = tmbinop Leq

(>==) :: Term -> Term -> Term
(>==) = tmbinop Geq

(>.) :: Term -> Term -> Term
(>.) = tmbinop Gt