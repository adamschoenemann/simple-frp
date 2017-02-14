
module FRP.TestPrograms where

import FRP.AST
import FRP.TestFunctions

prog_tails :: Program
prog_tails =
  let mainbd = TmLam "us" $
              (TmVar "tails" `TmApp` TmVar "us") `TmApp` (TmVar "nats" `TmApp` TmVar "us" `TmApp` TmLit (LInt 0))
      mainfn = frp_main mainbd (TyStream (TyStream TyNat))
  in  Program mainfn [frp_nats, frp_tails]

prog_map :: Program
prog_map =
  let mainfn = frp_main mainbd (TyStream TyNat)
      mainbd =
          TmLam "us" $
          ("map" `TmApp` "us" `TmApp` TmStable (TmLam "y" $ TmBinOp Mult (TmLit (LInt 2)) "y")) `TmApp`
          ("nats" `TmApp` "us" `TmApp` TmLit (LInt 0))

  in Program mainfn [frp_map, frp_nats]

prog_unfold :: Program
prog_unfold =
  let mainfn = frp_main (_body frp_fib) (TyStream TyNat)
  in Program mainfn [frp_unfold, frp_nats, frp_fib]

prog_swap_fib_nats = Program mainfn [frp_unfold, frp_fib, frp_nats, frp_swap]
  where
    mainfn = frp_main mainbd (TyStream TyNat)
    mainbd =
      TmLam "us" $
      "swap" `TmApp` "us" `TmApp` (TmLit $ LInt 10) `TmApp`
      ("nats" `TmApp` "us" `TmApp` (TmLit $ LInt 0)) `TmApp` ("fib" `TmApp` "us")