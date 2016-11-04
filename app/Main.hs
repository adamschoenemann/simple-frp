module Main where

import FRP
import FRP.AST
import FRP.Pretty

main :: IO ()
main = putStrLn "works"

{-
const : S alloc → N → S N
const us n =
  let cons(u, δ(us')) = us in
  let stable(x) = promote(n) in
  cons(x,δᵤ(const us' x))
-}
frp_const :: Decl
frp_const = Decl ty name body where
  ty = TyArr (TyStream TyAlloc) (TyArr TyNat (TyStream TyNat))
  name = "const"
  body = TmLam "us" (TmLam "n" lamBody)
  lamBody = TmLet pat1 rhs1 (TmLet pat2 rhs2 concl) where
    pat1 = PCons (PBind "u") (PDelay (PBind "us'"))
    rhs1 = TmVar "us"
    pat2 = PStable (PBind "x")
    rhs2 = TmPromote (TmVar "n")
    concl = TmCons (TmVar "x")
                   (TmDelay (TmVar "u")
                            (TmApp
                              (TmApp (TmVar "const") (TmVar "us'"))
                              (TmVar "x")
                            )
                   )
{-
sum acc : S alloc → S N → N → S N
sum acc us ns acc =
  let cons(u,δ(us')) = us in
  let cons(n,δ(ns')) = ns in
  let stable(x) = promote(n + acc) in
  cons(x, δ_u(sum_acc us' ns' x))

  ((sum_acc us') ns') x
  App (App (App sum_acc us') ns') x
-}
frp_sum_acc :: Decl
frp_sum_acc = Decl ty name body where
  ty = TyArr (TyStream TyAlloc)
             (TyArr (TyStream TyNat)
                    (TyArr TyNat
                           (TyStream TyNat)
                    )
             )
  name = "sum_acc"
  body = TmLam "us" (TmLam "ns" (TmLam "acc" lamBody))
  lamBody = TmLet pat1 rhs1 (TmLet pat2 rhs2 (TmLet pat3 rhs3 concl))
  pat1 = PCons (PBind "u") (PDelay (PBind "us'"))
  rhs1 = TmVar "us"
  pat2 = PCons (PBind "n") (PDelay (PBind "ns'"))
  rhs2 = TmVar "ns"
  pat3 = PStable (PBind "x")
  rhs3 = TmPromote (TmBinOp Add (TmVar "n") (TmVar "acc"))
  concl = TmCons (TmVar "x") (TmDelay (TmVar "u") delayBody)
  delayBody =
    TmApp (TmApp (TmApp (TmVar "sum_acc") (TmVar "us'"))
                 (TmVar "ns'"))
          (TmVar "x")

frp_const_10 :: Decl
frp_const_10 = Decl ty name body where
  ty = TyArr (TyStream TyAlloc) (TyStream TyNat)
  name = "const_10"
  body = TmApp (_body frp_const) (TmLit (LInt 10))

frp_constProg :: Program
frp_constProg = Program { _main = frp_const_10, _decls = []}