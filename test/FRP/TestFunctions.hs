
module FRP.TestFunctions where

import FRP.AST

frps = [ frp_nats, frp_sum_acc, frp_sum, frp_tails, frp_map
       , frp_unfold, frp_fib, frp_swap
       ]

frp_nats :: Decl
frp_nats = Decl ty name body where
  ty   = TyStream TyAlloc `TyArr` TyStream TyNat
  name = "nats"
  body =
      TmLam "us" (TmLam "n" (
        TmLet (PCons (PBind "u") (PDelay "us'")) (TmVar "us") (
        TmLet (PStable (PBind "x")) (TmPromote (TmVar "n")) (
        TmCons (TmVar "x") (TmDelay (TmVar "u")
          ((TmVar "nats") `TmApp` (TmVar "us'") `TmApp` (TmBinOp Add (TmVar "x") (TmLit (LInt 1)))))
        ))
      ))

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
  pat1 = PCons (PBind "u") (PDelay "us'")
  rhs1 = TmVar "us"
  pat2 = PCons (PBind "n") (PDelay "ns'")
  rhs2 = TmVar "ns"
  pat3 = PStable (PBind "x")
  rhs3 = TmPromote (TmBinOp Add (TmVar "n") (TmVar "acc"))
  concl = TmCons (TmVar "x") (TmDelay (TmVar "u") delayBody)
  delayBody = TmVar "sum_acc" `TmApp` TmVar "us'" `TmApp` TmVar "ns'" `TmApp` TmVar "x"

frp_sum :: Decl
frp_sum = Decl ty name body where
  name = "sum"
  ty   = TyStream TyAlloc `TyArr` TyStream TyNat `TyArr` TyStream TyNat
  body = TmLam "us" (TmLam "ns" (
         ((TmVar "sum_acc" `TmApp` TmVar "us") `TmApp` TmVar "ns") `TmApp` TmLit (LInt 0)
         ))

frp_tails :: Decl
frp_tails = Decl ty name body where
  name = "tails"
  ty   = TyStream TyAlloc `TyArr` TyStream "A" `TyArr` TyStream (TyStream "A")
  body = TmLam "us" $ TmLam "xs" $
         TmLet (consp "u" "us'") "us" $
         TmLet (consp "x" "xs'") "xs" $
         TmCons "xs" (TmDelay "u" ("tails" `TmApp` "us'" `TmApp` "xs'"))
  consp h t = PCons h (PDelay t)

frp_main :: Term -> Type -> Decl
frp_main bd retTy = Decl ty "main" bd where
  ty = TyStream TyAlloc `TyArr` retTy


frp_map :: Decl
frp_map = Decl ty name body where
  ty = TyStream TyAlloc `TyArr` (TyStable ("A" `TyArr` "B")) `TyArr`
       TyStream "A" `TyArr` TyStream "B"
  name = "map"
  body =
    TmLam "us" $ TmLam "h" $ TmLam "xs" $
      TmLet (PCons "u" $ PDelay "us'") "us" $
      TmLet (PCons "x" $ PDelay "xs'") "xs" $
      TmLet (PStable "f") "h" $
      TmCons ("f" `TmApp` "x") (TmDelay "u" $ "map" `TmApp` "us'" `TmApp` TmStable "f" `TmApp` "xs'")


frp_unfold :: Decl
frp_unfold = Decl ty name body where
  ty = TyStream TyAlloc `TyArr`
       TyStable ("X" `TyArr` ("A" `TyProd` TyLater "X")) `TyArr`
       "X" `TyArr`
       TyStream "A"
  name = "unfold"
  body =
    TmLam "us" $ TmLam "h" $ TmLam "x" $
    TmLet (PCons "u" $ PDelay "us'") "us" $
    TmLet (PStable "f") "h" $
    TmLet (PTup "a" $ PDelay "x'") ("f" `TmApp` "x") $
    TmCons "a" (TmDelay "u" $ "unfold" `TmApp` "us'" `TmApp` (TmStable "f") `TmApp` "x'")

frp_fib :: Decl
frp_fib = Decl ty name body where
 ty = TyStream TyAlloc `TyArr` TyStream TyNat
 name = "fib"
 body =
    TmLam "us" $
    TmLet (PCons "u" $ PDelay "us'") "us" $
    TmLet "fibfn" fiblam $
    "unfold" `TmApp` "us" `TmApp` TmStable ("fibfn" `TmApp` "u") `TmApp`
    TmTup (TmLit $ LInt 0) (TmLit $ LInt 1)
 fiblam = TmLam "u" $ TmLam "x" $
          TmLet (PTup "a" "b") "x" $
          TmLet "f" (TmBinOp Add "a" "b") $
          TmTup "f" (TmDelay "u" $ TmTup "b" "f")

frp_swap :: Decl
frp_swap = Decl ty name body where
  ty = TyStream TyAlloc `TyArr`
       TyNat `TyArr`
       TyStream "A" `TyArr`
       TyStream "A" `TyArr`
       TyStream "A"
  name = "swap"
  body = TmLam "us" $ TmLam "n" $ TmLam "xs" $ TmLam "ys" $
         TmITE (TmBinOp Eq "n" $ TmLit $ LInt 0)
            "ys" $
            TmLet (PCons "u" $ PDelay "us'") "us" $
            TmLet (PCons "x" $ PDelay "xs'") "xs" $
            TmLet (PCons "y" $ PDelay "ys'") "ys" $
            TmLet (PStable "m") (TmPromote "n")   $
            TmCons "x" (TmDelay "u" $ recCall)
  recCall = "swap" `TmApp` "us'" `TmApp` (TmBinOp Sub "m" (TmLit $ LInt 1)) `TmApp`
            "xs'" `TmApp` "ys'"

