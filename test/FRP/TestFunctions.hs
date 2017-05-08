{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}

module FRP.TestFunctions where

import FRP.AST
import FRP.AST.Reflect
import FRP.AST.Construct
import FRP.AST.QuasiQuoter

frps = [ frp_nats, frp_sum_acc, frp_sum, frp_tails, frp_map
       , frp_unfold, frp_fib_wrong, frp_swap
       ]

frp_const = unitFunc [unsafeDecl|
  const : S alloc -> Nat -> S Nat
  const us n =
    let cons(u, delay(us')) = us in
    let stable(x) = promote(n) in
    cons(x, delay(u, const us' x)).
|]

frp_const_fix = unitFunc [unsafeDecl|
  const : S alloc -> Nat -> S Nat
  const = fix f. \us n ->
    let cons(u, delay(us')) = us in
    let stable(x) = promote(n) in
    cons(x, delay(u, f us' x)).

|]


frp_nats = unitFunc [unsafeDecl|
  nats : S alloc -> Nat -> S Nat
  nats us n =
    let cons(u, delay(us')) = us in
    let stable(x) = promote(n) in
    cons(x, delay(u, nats us' (x + 1))).
|]

frp_sum_acc :: Decl ()
frp_sum_acc = unitFunc [unsafeDecl|
  sum_acc : S alloc -> S Nat -> Nat -> S Nat
  sum_acc us ns acc =
    let cons(u, delay(us')) = us in
    let cons(n, delay(ns')) = ns in
    let stable(x) = promote(n + acc) in
    cons(x, delay(u, (((sum_acc us') ns') x))).
|]

frp_sum :: Decl ()
frp_sum = unitFunc [unsafeDecl|
  sum : S alloc -> S Nat -> S Nat
  sum us ns = sum_acc us ns 0.
|]


frp_tails :: Decl ()
frp_tails = unitFunc [unsafeDecl|
  tails : S alloc -> S a -> S (S a)
  tails us xs =
    let cons(u, delay(us')) = us in
    let cons(x, delay(xs')) = xs in
    cons(xs, delay(u, ((tails us') xs'))).
|]

frp_map :: Decl ()
frp_map = unitFunc frp_map_sp

frp_map_sp = [unsafeDecl|
  map : S alloc -> #(A -> B) -> S A -> S B
  map us h xs =
    let cons(u, delay(us')) = us in
    let cons(x, delay(xs')) = xs in
    let stable(f) = h in
    cons((f x), delay(u, (((map us') stable(f)) xs'))).
|]


frp_prog_1 = [unsafeProg|

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

frp_unfold = unitFunc [unsafeDecl|
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
frp_natfn = unitFunc [unsafeDecl|
  natfn : (S alloc * Nat) -> (Nat * @(S alloc * Nat))
  natfn x =
    let (us, n) = x in
    let cons(u, delay(us')) = us in
    let stable(n') = promote(n) in
    (n, delay(u, (us', n' + 1))).
|]

frp_nats_unfold = unitFunc [unsafeDecl|
  nats : S alloc -> S Nat
  nats us =
    let fn = stable(natfn) in
    unfold us fn (us, 0).
|]

frp_swap :: Decl ()
frp_swap = unitFunc [unsafeDecl|
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

-- switch : S alloc -> S a -> E (S a) -> S a
frp_switch :: Decl ()
frp_switch = unitFunc [unsafeDecl|
  switch : S alloc -> S a -> (mu b. (S a) + b) -> S a
  switch us xs e =
    let cons(u, delay(us')) = us in
    let cons(x, delay(xs')) = xs in
    case out (mu b. (S a) + b) e of
      | inl ys -> ys
      | inr t  -> let delay(e') = t in
                  cons(x, delay (u, switch us' xs' e')).
|]

frp_bind :: Decl ()
frp_bind = unitFunc [unsafeDecl|
  bind : S alloc -> #(a -> (mu af. b + af)) -> (mu af. a + af) -> (mu af. b + af)
  bind us h e =
    let cons(u,delay(us')) = us in
    let stable(f) = h in
    case out (mu af. a + af) e of
      | inl a -> f a
      | inr t ->
          let delay(e') = t in
          into (mu af. b + af) (inr delay(u, bind us' stable(f) e')).
|]

frp_main :: EvalTerm -> Type () -> Decl ()
frp_main bd retTy = Decl () ty "main" bd where
  ty = tystream tyalloc |-> retTy

declTy_01 :: FRP TNat
declTy_01 = [decl|
  ex01 : Nat
  ex01 = 10.
|]

declTy_02 :: FRP (TNat :->: TNat)
declTy_02 = [decl|
  ex02 : Nat -> Nat
  ex02 x = x * 10.
|]

declTy_03 :: FRP ((TNat :*: TBool) :->: TNat)
declTy_03 = [decl|
  ex03 : (Nat * Bool) -> Nat
  ex03 x =
    let (n, b) = x in if b then n * 2 else n + 2.
|]

frp_incr :: FRP (TStream TAlloc :->: TStream TNat :->: TStream TNat)
frp_incr = [decl|
  main : S alloc -> S Nat -> S Nat
  main us xs =
    let map = fix (map : S alloc -> #(a -> b) -> S a -> S b). \us h xs ->
        let cons(u, delay(us')) = us in
        let cons(x, delay(xs')) = xs in
        let stable(f) = h in
        cons((f x), delay(u, (((map us') stable(f)) xs'))) in
    map us stable(\x -> x + 1) xs.
|]

frp_incr_fails :: Decl ()
frp_incr_fails = unitFunc [unsafeDecl|
  incr : S alloc -> S Nat -> S Nat
  incr allocs lst =
    let map = fix (map : S alloc -> #(a -> b) -> S a -> S b). \us h xs ->
        let cons(u, delay(us')) = us in
        let cons(x, delay(xs')) = xs in
        let stable(f) = h in
        cons(f x, delay(u, (((map us') stable(f)) xs'))) in
    map allocs (\x -> x + 1) lst.
|]

frp_tails_ty :: FRP (TStream TAlloc :->: TStream TNat :->: TStream (TStream TNat))
frp_tails_ty = [decl|
  tails : S alloc -> S Nat -> S (S Nat)
  tails us xs =
    let cons(u, delay(us')) = us in
    let cons(x, delay(xs')) = xs in
    cons(xs, delay(u, ((tails us') xs'))).
|]

frp_incr_prog_ty :: FRP (TStream TAlloc :->: TStream TNat :->: TStream TNat)
frp_incr_prog_ty = [prog|
  map : S alloc -> #(a -> b) -> S a -> S b
  map us h xs =
    let cons(u, delay(us')) = us in
    let cons(x, delay(xs')) = xs in
    let stable(f) = h in
    cons(f x, delay(u, (((map us') stable(f)) xs'))).


  main : S alloc -> S Nat -> S Nat
  main allocs lst =
    map allocs stable(\x -> x + 1) lst.
|]

frp_scary_const_fails :: Decl ()
frp_scary_const_fails = unitFunc [unsafeDecl|
  scary_const : S alloc -> S Nat -> S (S Nat)
  scary_const us ns =
    let cons(u, delay(us')) = us in
    let stable(xs) = promote(ns) in
    cons(xs, delay(u, scary_const us' xs)).
|]

frp_scary_const :: FRP (TStream TAlloc :->: TStream (TStream TNat))
frp_scary_const = [prog|
  buffer : S alloc -> Nat -> S Nat -> S Nat
  buffer us n xs =
    let cons(u, delay(us')) = us in
    let cons(x, delay(xs')) = xs in
    let stable(x') = promote(x) in
    cons(n, delay(u, buffer us' x' xs')).

  forward : S alloc -> S Nat -> @(S Nat)
  forward us xs =
    let cons(u, delay(us')) = us in
    let cons(x, delay(xs')) = xs in
    let stable(x') = promote(x) in
    delay(u, buffer us' x' xs').

  scary_const : S alloc -> S Nat -> S (S Nat)
  scary_const us xs =
    let cons(u, delay(us')) = us in
    let delay(xs') = forward us xs in
    cons(xs, delay(u, scary_const us' xs')).

  nats : S alloc -> Nat -> S Nat
  nats us n =
    let cons(u, delay(us')) = us in
    let stable(x) = promote(n) in
    cons(x, delay(u, nats us' (x + 1))).

  main : S alloc -> S (S Nat)
  main us = scary_const us (nats us 0).
|]

frp_fixedpoint = [prog|
  selfapp : (@a -> a) -> S alloc -> @(mu af. #(S alloc -> af -> a)) -> a
  selfapp f us v =
    let cons(u, delay(us')) = us in
    let delay(x) = v in
    f delay(u,
      let stable(w) = out (mu af. #(S alloc -> af -> a)) x in
      let cons(u', us'') = us' in
      let y = delay(u', into (mu af. #(S alloc -> af -> a)) stable(w)) in
      w us' y
    ).


  fixedpoint : #(@a -> a) -> S alloc -> a
  fixedpoint h us =
    let cons(u, delay(us')) = us in
    let stable(f) = h in
    let delay(y) = delay(u, into (mu af. #(S alloc -> af -> a)) stable(selfapp f)) in
    selfapp f us delay(u,y).


  ones : S alloc -> S Nat
  ones us =
    let fn = stable(\xs -> cons(1, xs)) in
    fixedpoint fn us.

  main : S alloc -> S Nat
  main us = ones us.
|]

frp_ones :: FRP (TStream TAlloc :->: TStream TNat)
frp_ones = [prog|
  const : S alloc -> Nat -> S Nat
  const us n =
    let cons(u, delay(us')) = us in
    let stable(x) = promote(n) in
    cons(x, delay(u, const us' x)).

  main : S alloc -> S Nat
  main us = const us 1.
|]

frp_switch_safe :: FRP (TStream TAlloc :->: TStream TNat :->: TStream TNat)
frp_switch_safe = [prog|
  nats : S alloc -> Nat -> S Nat
  nats us n =
    let cons(u, delay(us')) = us in
    let stable(x) = promote(n) in
    cons(x, delay(u, nats us' (x + 1))).

  switch : S alloc -> S a -> (mu f. S a + f) -> S a
  switch us xs e =
    let cons(u, delay(us')) = us in
    let cons(x, delay(xs')) = xs in
    case out (mu f. (S a) + f) e of
      | inl ys -> ys
      | inr t  -> let delay(e') = t in
                  cons(x, delay (u, switch us' xs' e')).

  eventually : S alloc -> Nat -> S a -> (mu f. S a + f)
  eventually us n xs =
    if n == 0
      then into (mu f. S a + f) inl xs
      else let cons(u, delay(us')) = us in
           let cons(x, delay(xs')) = xs in
           let stable(n') = promote(n)  in
           into (mu f. S a + f) inr delay(u, eventually us' (n' - 1) xs').

  main : S alloc -> S Nat -> S Nat
  main us xs =
    let e = eventually us 5 (nats us 0) in
    switch us xs e.
|]

hsterm_01 = [hsterm| \x -> x + x |]
hsterm_02 = [hsterm|
  fix nats. \us n ->
    let cons(u, delay(us')) = us in
    let stable(x) = promote(n) in
    cons(x, delay(u, nats us' (x + 1)))
|]

[hsprog|
  const' : S alloc -> Nat -> S Nat
  const' us n =
    let cons(u, delay(us')) = us in
    let stable(x) = promote(n) in
    cons(x, delay(u, const' us' x)).
|]

[hsprog|

  import const'.

  nats : S alloc -> Nat -> S Nat
  nats us n =
    let cons(u, delay(us')) = us in
    let stable(x) = promote(n) in
    cons(x, delay(u, nats us' (x + 1))).

  switch : S alloc -> S a -> (mu f. S a + f) -> S a
  switch us xs e =
    let cons(u, delay(us')) = us in
    let cons(x, delay(xs')) = xs in
    case out (mu f. (S a) + f) e of
      | inl ys -> ys
      | inr t  -> let delay(e') = t in
                  cons(x, delay (u, switch us' xs' e')).

  eventually : S alloc -> Nat -> S a -> (mu f. S a + f)
  eventually us n xs =
    if n == 0
      then into (mu f. S a + f) inl xs
      else let cons(u, delay(us')) = us in
           let cons(x, delay(xs')) = xs in
           let stable(n') = promote(n)  in
           into (mu f. S a + f) inr delay(u, eventually us' (n' - 1) xs').

  fiveThenNats : S alloc -> S Nat -> S Nat
  fiveThenNats us xs =
    let e = eventually us 5 (nats us 0) in
    switch us xs e.
|]

prog_tails :: Program ()
prog_tails =
  let mainbd = "us" -->
              ("tails" <| "us") <| ("nats" <| "us" <| 0)
      mainfn = frp_main mainbd (tystream (tystream tynat))
  in  Program [] [mainfn, frp_nats, frp_tails]

prog_map :: Program ()
prog_map =
  let mainfn = frp_main mainbd (tystream tynat)
      mainbd =
          "us" -->
          ("map" <| "us" <| tmstable ("y" --> 2 * "y")) <|
          ("nats" <| "us" <| 0)

  in Program [] [mainfn, frp_map, frp_nats]

prog_unfold :: Program ()
prog_unfold =
  let mainfn = frp_main (_body frp_nats_unfold) (tystream tynat)
  in Program [] [mainfn, frp_unfold, frp_natfn, frp_nats_unfold]

prog_swap_const_nats = Program [] [mainfn, frp_unfold, frp_const, frp_nats, frp_swap]
  where
    mainfn = frp_main mainbd (tystream tynat)
    mainbd =
      "us" -->
      "swap" <| "us" <| 10 <|
      ("nats" <| "us" <| 0) <| ("const" <| "us" <| 42)

prog_sum = Program [] [mainfn, frp_nats, frp_sum_acc, frp_sum] where
  mainbd = "us" -->
              ("sum" <| "us") <| ("nats" <| "us" <| 0)
  mainfn = frp_main mainbd (tystream tynat)