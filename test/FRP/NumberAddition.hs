{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

module FRP.NumberAddition where

import FRP
import FRP.AST.Reflect
import FRP.AST.QuasiQuoter
import FRP.TestFunctions (frp_tails_ty)

frp_add :: FRP (TStream TAlloc :->: TStream (TNat :*: TNat) :->: TStream TNat)
frp_add = [prog|
  main : S alloc -> S (Nat * Nat) -> S Nat
  main us ps =
    let cons(u, delay(us')) = us in
    let cons((x,y), delay(ps')) = ps in
    cons(x+y, delay(u, main us' ps')).
|]

main :: IO ()
main = interact (unlines . process . lines) where
  process = map (("result: " ++) . (show :: Int -> String)) . transform frp_add .
            map (read :: String -> (Int,Int))

-- main :: IO ()
-- main = putStrLn . show . map (take 100) . transform frp_tails_ty $ [1..]
