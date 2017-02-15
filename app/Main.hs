module Main where

import FRP
import FRP.AST
import FRP.AST.Construct
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
frp_const :: Decl ()
frp_const = Decl ty name body where
  ty = TyArr (TyStream TyAlloc) (TyArr TyNat (TyStream TyNat))
  name = "const"
  body = tmlam "us" (tmlam "n" lamBody)
  lamBody = tmlet pat1 rhs1 (tmlet pat2 rhs2 concl) where
    pat1 = PCons (PBind "u") (PDelay "us'")
    rhs1 = tmvar "us"
    pat2 = PStable (PBind "x")
    rhs2 = tmpromote (tmvar "n")
    concl = tmcons (tmvar "x")
                   (tmdelay (tmvar "u")
                            (tmapp
                              (tmapp (tmvar "const") (tmvar "us'"))
                              (tmvar "x")
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
frp_sum_acc :: Decl ()
frp_sum_acc = Decl ty name body where
  ty = TyArr (TyStream TyAlloc)
             (TyArr (TyStream TyNat)
                    (TyArr TyNat
                           (TyStream TyNat)
                    )
             )
  name = "sum_acc"
  body = tmlam "us" (tmlam "ns" (tmlam "acc" lamBody))
  lamBody = tmlet pat1 rhs1 (tmlet pat2 rhs2 (tmlet pat3 rhs3 concl))
  pat1 = PCons (PBind "u") (PDelay "us'")
  rhs1 = tmvar "us"
  pat2 = PCons (PBind "n") (PDelay "ns'")
  rhs2 = tmvar "ns"
  pat3 = PStable (PBind "x")
  rhs3 = tmpromote (tmbinop Add (tmvar "n") (tmvar "acc"))
  concl = tmcons (tmvar "x") (tmdelay (tmvar "u") delayBody)
  delayBody =
    tmapp (tmapp (tmapp (tmvar "sum_acc") (tmvar "us'"))
                 (tmvar "ns'"))
          (tmvar "x")

frp_const_10 :: Decl ()
frp_const_10 = Decl ty name body where
  ty = TyArr (TyStream TyAlloc) (TyStream TyNat)
  name = "const_10"
  body = case frp_const of
    Decl _ty _nm body -> tmapp (unitFunc body) (tmlit (LInt 10))

frp_constProg :: Program ()
frp_constProg = Program { _main = frp_const_10, _decls = []}