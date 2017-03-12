{-# LANGUAGE QuasiQuotes #-}

module FRP.TestFunctions where

import FRP.AST
import FRP.AST.Construct
import FRP.AST.QuasiQuoter

frps = [ frp_nats, frp_sum_acc, frp_sum, frp_tails, frp_map
       , frp_unfold, frp_fib_wrong, frp_swap
       ]

frp_const = unitFunc [decl|
  const : S alloc -> Nat -> S Nat
  const us n =
    let cons(u, delay(us')) = us in
    let stable(x) = promote(n) in
    cons(x, delay(u, const us' x)).
|]

frp_nats :: Decl ()
frp_nats = Decl () ty name body where
  ty   = tystream tyalloc |-> tynat |-> tystream tynat
  name = "nats"
  body =
      "us" --> "n" -->
        tmlet (PCons (PBind "u") (PDelay "us'")) "us" (
        tmlet (PStable (PBind "x")) (tmpromote "n") (
        tmcons "x" (tmdelay "u"
          ("nats" <| "us'" <| ("x" + 1)))
        ))

frp_nats' = [decl|
  nats : S alloc -> Nat -> S Nat
  nats us n =
    let cons(u, delay(us')) = us in
    let stable(x) = promote(n) in
    cons(x, delay(u, nats us' (x + 1))).
|]

frp_sum_acc :: Decl ()
frp_sum_acc = Decl () ty name body where
  ty = tystream tyalloc |-> tystream tynat |-> tynat |-> tystream tynat
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
frp_sum = Decl () ty name body where
  name = "sum"
  ty   = tystream tyalloc |-> tystream tynat |-> tystream tynat
  body = "us" --> "ns" -->
         ("sum_acc" <| "us" <| "ns") <| 0


frp_tails :: Decl ()
frp_tails = Decl () ty name body where
  name = "tails"
  ty   = tystream tyalloc |-> tystream "A" |-> tystream (tystream "A")
  body = "us" --> "xs" -->
         tmlet (consp "u" "us'") "us" $
         tmlet (consp "x" "xs'") "xs" $
         tmcons "xs" (tmdelay "u" ("tails" <| "us'" <| "xs'"))
  consp h t = PCons h (PDelay t)

frp_main :: EvalTerm -> Type () -> Decl ()
frp_main bd retTy = Decl () ty "main" bd where
  ty = tystream tyalloc |-> retTy


frp_map :: Decl ()
frp_map = Decl () ty name body where
  ty = tystream tyalloc |-> tystable ("A" |-> "B") |->
       tystream "A" |-> tystream "B"
  name = "map"
  body =
    "us" --> "h" --> "xs" -->
      tmlet (PCons "u" $ PDelay "us'") "us" $
      tmlet (PCons "x" $ PDelay "xs'") "xs" $
      tmlet (PStable "f") "h" $
      tmcons ("f" <| "x") (tmdelay "u" $ "map" <| "us'" <| tmstable "f" <| "xs'")


frp_unfold' :: Decl ()
frp_unfold' = Decl () ty name body where
  ty = tystream tyalloc |->
       tystable ("X" |-> ("A" `typrod` tylater "X")) |->
       "X" |->
       tystream "A"
  name = "unfold"
  body =
    "us" --> "h" --> "x" -->
    tmlet (PCons "u" $ PDelay "us'") "us" $
    tmlet (PStable "f") "h" $
    tmlet (PTup "a" $ PDelay "x'") ("f" <| "x") $
    tmcons "a" (tmdelay "u" ("unfold" <| "us'" <| (tmstable "f") <| "x'"))

frp_unfold = unitFunc [decl|
  unfold : S alloc -> #(X -> (A * @X)) -> X -> S A
  unfold us h x =
    let cons(u, delay(us')) = us in
    let stable(f) = h in
    let (a, delay(x')) = f x in
    cons(a, delay(u, unfold us' stable(f) x')).
|]

-- should not type-check!
frp_fib_wrong :: Decl ()
frp_fib_wrong = Decl () ty name body where
 ty = tystream tyalloc |-> tystream tynat
 name = "fib"
 body =
    "us" -->
    tmlet (PCons "u" $ PDelay "us'") "us" $
    tmlet "fibfun" fibfn $
    tmlet (PStable "fibfn") (tmpromote "fibfun") $
    "unfold" <| "us" <| tmstable ("fibfn" <| "u") <| tmtup 0 1
 fibfn =  tmlamty "u" tyalloc $ tmlamty "x" (typrod tynat tynat) $
          tmlet (PTup "a" "b") "x" $
          tmlet "f" ("a" + "b") $
          tmlet (PStable "b'") (tmpromote "b") $
          tmlet (PStable "f'") (tmpromote "f") $
          tmtup "f" (tmdelay "u" (tmtup (tmstable "b'") (tmstable "f'")))

frp_natfn = unitFunc [decl|
  natfn : (S alloc * Nat) -> (Nat * @(S alloc * Nat))
  natfn x =
    let (us, n) = x in
    let cons(u, delay(us')) = us in
    let stable(n') = promote(n) in
    (n, delay(u, (us', n' + 1))).
|]

frp_nats_unfold = unitFunc [decl|
  nats : S alloc -> S Nat
  nats us =
    let fn = stable(natfn) in
    unfold us fn (us, 0).
|]

frp_swap :: Decl ()
frp_swap = Decl () ty name body where
  ty = tystream tyalloc |->
       tynat |->
       tystream "A" |->
       tystream "A" |->
       tystream "A"
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

