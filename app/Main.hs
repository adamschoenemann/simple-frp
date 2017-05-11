{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}

module Main where

import FRP
import FRP.AST.Reflect

-- frp_incr :: FRP (TStream TAlloc :->: TStream TNat)
frp_incr = [prog|
  const : S alloc -> Nat -> S Nat
  const us n =
    let cons(u, delay(us')) = us in
    let stable(x) = promote(n) in
    cons(x, delay(u, const us' x)).

  map : S alloc -> #(a -> b) -> S a -> S b
  map us h xs =
      let cons(u, delay(us')) = us in
      let cons(x, delay(xs')) = xs in
      let stable(f) = h in
      cons(f x, delay(u, map us' stable(f) xs')).

  main : S alloc -> S Nat -> S Nat
  main us xs =
    -- let xs = const us 0 in
    map us stable(\x -> x + 1) xs.
|]

-- frp_switch_safe :: FRP (TStream TAlloc :->: TStream TNat :->: TStream TNat)
frp_switch_safe = [prog|
  const : S alloc -> Nat -> S Nat
  const us n =
    let cons(u, delay(us')) = us in
    let stable(x) = promote(n) in
    cons(x, delay(u, const us' x)).

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
    let e = eventually us 100 (nats us 0) in
    -- let xs = const us 0 in
    switch us xs e.
|]

main :: IO ()
main = do
  let xs = transform' frp_switch_safe [100,99..]
  putStrLn . show $ take 10000000 xs