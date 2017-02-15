
module FRP.TestPrograms where

import FRP.AST
import FRP.AST.Construct
import FRP.TestFunctions

prog_tails :: Program ()
prog_tails =
  let mainbd = "us" -->
              ("tails" <| "us") <| ("nats" <| "us" <| 0)
      mainfn = frp_main mainbd (TyStream (TyStream TyNat))
  in  Program mainfn [frp_nats, frp_tails]

prog_map :: Program ()
prog_map =
  let mainfn = frp_main mainbd (TyStream TyNat)
      mainbd =
          "us" -->
          ("map" <| "us" <| tmstable ("y" --> 2 * "y")) <|
          ("nats" <| "us" <| 0)

  in Program mainfn [frp_map, frp_nats]

prog_unfold :: Program ()
prog_unfold =
  let mainfn = frp_main (_body frp_fib) (TyStream TyNat)
  in Program mainfn [frp_unfold, frp_nats, frp_fib]

prog_swap_fib_nats = Program mainfn [frp_unfold, frp_fib, frp_nats, frp_swap]
  where
    mainfn = frp_main mainbd (TyStream TyNat)
    mainbd =
      "us" -->
      "swap" <| "us" <| 10 <|
      ("nats" <| "us" <| 0) <| ("fib" <| "us")

prog_sum = Program mainfn [frp_nats, frp_sum_acc, frp_sum] where
  mainbd = "us" -->
              ("sum" <| "us") <| ("nats" <| "us" <| 0)
  mainfn = frp_main mainbd (TyStream TyNat)