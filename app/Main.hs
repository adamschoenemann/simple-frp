{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LiberalTypeSynonyms #-}

module Main where

import FRP
import FRP.AST.Reflect
import Data.Function (fix)

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

[hsprog|
  const' : S alloc -> Nat -> S Nat
  const' us n =
    let cons(u, delay(us')) = us in
    let stable(x) = promote(n) in
    cons(x, delay(u, const' us' x)).

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

  frp_main : S alloc -> S Nat -> S Nat
  frp_main us xs =
    let e = eventually us 100 (nats us 0) in
    switch us xs e.
|]

[hsprog|
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

  nats' : S alloc -> Nat -> S Nat
  nats' us n =
    let cons(u, delay(us')) = us in
    let stable(x) = promote(n) in
    cons(x, delay(u, nats' us' (x + 1))).

  scary_main : S alloc -> S (S Nat)
  scary_main us = scary_const us (nats' us 0).
|]

-- [hsprog|

-- selfapp : (@a -> a) -> S alloc -> @(mu af. #(S alloc -> af -> a)) -> a
-- selfapp f us v =
--   let cons(u, delay(us')) = us in
--   let delay(x) = v in
--   f delay(u,
--     let stable(w) = out (mu af. #(S alloc -> af -> a)) x in
--     let cons(u', us'') = us' in
--     let y = delay(u', into (mu af. #(S alloc -> af -> a)) stable(w)) in
--     w us' y
--   ).


-- fixedpoint : #(@a -> a) -> S alloc -> a
-- fixedpoint h us =
--   let cons(u, delay(us')) = us in
--   let stable(f) = h in
--   let delay(y) = delay(u, into (mu af. #(S alloc -> af -> a)) stable(selfapp f)) in
--   selfapp f us delay(u,y).


-- ones : S alloc -> S Nat
-- ones us =
--   let fn = stable(\xs -> cons(1, xs)) in
--   fixedpoint fn us.

-- fix_main : S alloc -> S Nat
-- fix_main us = ones us.
-- |]

newtype Fun a b c = Fun {unFun :: a -> c -> b}

selfapp :: (a -> a) -> [()] -> Mu (Fun [()] a) -> a
selfapp f us v =
  let u : us' = us
      x = v
  in f (let w         = unFun . out $ x
            u' : us'' = us'
            y         = Into (Fun w)
        in w us' y)

allocs = () : allocs

main :: IO ()
main = do
  -- let xs = fix_main allocs
  -- putStrLn . show . take 100000 $ xs

  let xs = scary_main allocs [100 :: Int,99..] :: [Int]
  putStrLn . show $ take 10000000 xs

-- main :: IO ()
-- main = do
--   let xs = transform frp_switch_safe [100 :: Int,99..] :: [Int]
--   putStrLn . show $ take 10000000 xs