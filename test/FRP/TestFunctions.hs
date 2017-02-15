
module FRP.TestFunctions where

import FRP.AST
import FRP.AST.Construct

frps = [ frp_nats, frp_sum_acc, frp_sum, frp_tails, frp_map
       , frp_unfold, frp_fib, frp_swap
       ]

frp_nats :: Decl ()
frp_nats = Decl ty name body where
  ty   = TyStream TyAlloc `TyArr` TyStream TyNat
  name = "nats"
  body =
      "us" --> "n" -->
        tmlet (PCons (PBind "u") (PDelay "us'")) "us" (
        tmlet (PStable (PBind "x")) (tmpromote "n") (
        tmcons "x" (tmdelay "u"
          ("nats" <| "us'" <| ("x" + 1)))
        ))

frp_sum_acc :: Decl ()
frp_sum_acc = Decl ty name body where
  ty = TyArr (TyStream TyAlloc)
             (TyArr (TyStream TyNat)
                    (TyArr TyNat
                           (TyStream TyNat)
                    )
             )
  name = "sum_acc"
  body = "us" --> "ns" --> "acc" --> lamBody
  lamBody = tmlet pat1 rhs1 (tmlet pat2 rhs2 (tmlet pat3 rhs3 concl))
  pat1 = PCons (PBind "u") (PDelay "us'")
  rhs1 = "us"
  pat2 = PCons (PBind "n") (PDelay "ns'")
  rhs2 = "ns"
  pat3 = PStable (PBind "x")
  rhs3 = tmpromote (tmbinop Add "n" "acc")
  concl = tmcons "x" (tmdelay "u" delayBody)
  delayBody = "sum_acc" <| "us'" <| "ns'" <| "x"

frp_sum :: Decl ()
frp_sum = Decl ty name body where
  name = "sum"
  ty   = TyStream TyAlloc `TyArr` TyStream TyNat `TyArr` TyStream TyNat
  body = "us" --> "ns" -->
         ("sum_acc" <| "us" <| "ns") <| 0


frp_tails :: Decl ()
frp_tails = Decl ty name body where
  name = "tails"
  ty   = TyStream TyAlloc `TyArr` TyStream "A" `TyArr` TyStream (TyStream "A")
  body = "us" --> "xs" -->
         tmlet (consp "u" "us'") "us" $
         tmlet (consp "x" "xs'") "xs" $
         tmcons "xs" (tmdelay "u" ("tails" <| "us'" <| "xs'"))
  consp h t = PCons h (PDelay t)

frp_main :: EvalTerm -> Type -> Decl ()
frp_main bd retTy = Decl ty "main" bd where
  ty = TyStream TyAlloc `TyArr` retTy


frp_map :: Decl ()
frp_map = Decl ty name body where
  ty = TyStream TyAlloc `TyArr` TyStable ("A" `TyArr` "B") `TyArr`
       TyStream "A" `TyArr` TyStream "B"
  name = "map"
  body =
    "us" --> "h" --> "xs" -->
      tmlet (PCons "u" $ PDelay "us'") "us" $
      tmlet (PCons "x" $ PDelay "xs'") "xs" $
      tmlet (PStable "f") "h" $
      tmcons ("f" <| "x") (tmdelay "u" $ "map" <| "us'" <| tmstable "f" <| "xs'")


frp_unfold :: Decl ()
frp_unfold = Decl ty name body where
  ty = TyStream TyAlloc `TyArr`
       TyStable ("X" `TyArr` ("A" `TyProd` TyLater "X")) `TyArr`
       "X" `TyArr`
       TyStream "A"
  name = "unfold"
  body =
    "us" --> "h" --> "x" -->
    tmlet (PCons "u" $ PDelay "us'") "us" $
    tmlet (PStable "f") "h" $
    tmlet (PTup "a" $ PDelay "x'") ("f" <| "x") $
    tmcons "a" (tmdelay "u" ("unfold" <| "us'" <| (tmstable "f") <| "x'"))

frp_fib :: Decl ()
frp_fib = Decl ty name body where
 ty = TyStream TyAlloc `TyArr` TyStream TyNat
 name = "fib"
 body =
    "us" -->
    tmlet (PCons "u" $ PDelay "us'") "us" $
    tmlet "fibfn" fibfn $
    "unfold" <| "us" <| tmstable ("fibfn" <| "u") <| tmtup 0 1
 fibfn = "u" --> "x" -->
          tmlet (PTup "a" "b") "x" $
          tmlet "f" ("a" + "b") $
          tmtup "f" (tmdelay "u" (tmtup "b" "f"))

frp_swap :: Decl ()
frp_swap = Decl ty name body where
  ty = TyStream TyAlloc `TyArr`
       TyNat `TyArr`
       TyStream "A" `TyArr`
       TyStream "A" `TyArr`
       TyStream "A"
  name = "swap"
  body = "us" --> "n" --> "xs" --> "ys" -->
         tmite (tmbinop Eq "n" 0)
            "ys" $
            tmlet (PCons "u" $ PDelay "us'") "us" $
            tmlet (PCons "x" $ PDelay "xs'") "xs" $
            tmlet (PCons "y" $ PDelay "ys'") "ys" $
            tmlet (PStable "m") (tmpromote "n")   $
            tmcons "x" (tmdelay "u" $ recCall)
  recCall = "swap" <| "us'" <| (tmbinop Sub "m" $ 1) <|
            "xs'" <| "ys'"

