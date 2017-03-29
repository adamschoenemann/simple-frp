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

frp_const_fix = unitFunc [decl|
  const : S alloc -> Nat -> S Nat
  const = fix f. \us n ->
    let cons(u, delay(us')) = us in
    let stable(x) = promote(n) in
    cons(x, delay(u, f us' x)).
|]


frp_nats = unitFunc [decl|
  nats : S alloc -> Nat -> S Nat
  nats us n =
    let cons(u, delay(us')) = us in
    let stable(x) = promote(n) in
    cons(x, delay(u, nats us' (x + 1))).
|]

frp_sum_acc :: Decl ()
frp_sum_acc = unitFunc [decl|
  sum_acc : S alloc -> S Nat -> Nat -> S Nat
  sum_acc us ns acc =
    let cons(u, delay(us')) = us in
    let cons(n, delay(ns')) = ns in
    let stable(x) = promote(n + acc) in
    cons(x, delay(u, (((sum_acc us') ns') x))).
|]

frp_sum :: Decl ()
frp_sum = unitFunc [decl|
  sum : S alloc -> S Nat -> S Nat
  sum us ns = sum_acc us ns 0.
|]


frp_tails :: Decl ()
frp_tails = unitFunc [decl|
  tails : S alloc -> S A -> S (S A)
  tails us xs =
    let cons(u, delay(us')) = us in
    let cons(x, delay(xs')) = xs in
    cons(xs, delay(u, ((tails us') xs'))).
|]

frp_map :: Decl ()
frp_map = unitFunc [decl|
  map : S alloc -> #(A -> B) -> S A -> S B
  map us h xs =
    let cons(u, delay(us')) = us in
    let cons(x, delay(xs')) = xs in
    let stable(f) = h in
    cons((f x), delay(u, (((map us') stable(f)) xs'))).
|]

-- this could be a way
-- data FRPTy : * -> * where
--   Simple : AST -> FRPTy [Nat]
--   Trans  : AST -> FRPTy ([Nat] -> [Nat])

frp_prog_1 = [prog|

  map : S alloc -> #(A -> B) -> S A -> S B
  map us h xs =
    let cons(u, delay(us')) = us in
    let cons(x, delay(xs')) = xs in
    let stable(f) = h in
    cons((f x), delay(u, (((map us') stable(f)) xs'))).

  nats : S alloc -> Nat -> S Nat
  nats us n =
    let cons(u, delay(us')) = us in
    let stable(x) = promote(n) in
    cons(x, delay(u, nats us' (x + 1))).

  main : S alloc -> S Int -> S Nat
  main us xs = nats us 0.

|]


-- frp_unfold' :: Decl ()
-- frp_unfold' = Decl () ty name body where
--   ty = tystream tyalloc |->
--        tystable ("X" |-> ("A" `typrod` tylater "X")) |->
--        "X" |->
--        tystream "A"
--   name = "unfold"
--   body =
--     "us" --> "h" --> "x" -->
--     tmlet (PCons "u" $ PDelay "us'") "us" $
--     tmlet (PStable "f") "h" $
--     tmlet (PTup "a" $ PDelay "x'") ("f" <| "x") $
--     tmcons "a" (tmdelay "u" ("unfold" <| "us'" <| (tmstable "f") <| "x'"))

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

frp_natfn :: Decl ()
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
frp_swap = unitFunc [decl|
  swap : S alloc -> Nat -> S A -> S A -> S A
  swap us n xs ys =
    if n == 0
      then ys
      else let cons(u, delay(us')) = us in
           let cons(x, delay(xs')) = xs in
           let cons(y, delay(ys')) = ys in
           let stable(m) = promote(n) in
           cons(x, delay(u, ((((swap us') (m - 1)) xs') ys'))).
|]

frp_test :: Decl ()
frp_test = unitFunc [decl|
  fn : Nat
  fn = $(hskIntToNat 10)
|]

-- switch : S alloc -> S a -> E (S a) -> S a
frp_switch :: Decl ()
frp_switch = unitFunc [decl|
  switch : S alloc -> S a -> S a -> S a
  switch us xs e =
    let cons(u, delay(us')) = us in
    let cons(x, delay(xs')) = xs in
    case out e of
      | inl ys -> ys
      | inr t  -> let delay(e') = t in
                  cons(x, delay (u, switch us' xs' e')).
|]


frp_main :: EvalTerm -> Type () -> Decl ()
frp_main bd retTy = Decl () ty "main" bd where
  ty = tystream tyalloc |-> retTy