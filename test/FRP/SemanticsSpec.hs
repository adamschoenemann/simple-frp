
module FRP.SemanticsSpec where

import Test.Hspec
import FRP.AST
import FRP.Semantics
import FRP.Pretty

import Control.Monad.State
import Debug.Trace
import qualified Data.Map.Strict as M
import Data.List (unfoldr)

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

prog_tails :: Program
prog_tails =
  let mainbd = TmLam "us" $
              (TmVar "tails" `TmApp` TmVar "us") `TmApp` (TmVar "nats" `TmApp` TmVar "us" `TmApp` TmLit (LInt 0))
      mainfn = frp_main mainbd (TyStream (TyStream TyNat))
  in  Program mainfn [frp_nats, frp_tails]

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

prog_map :: Program
prog_map =
  let mainfn = frp_main mainbd (TyStream TyNat)
      mainbd =
          TmLam "us" $
          ("map" `TmApp` "us" `TmApp` TmStable (TmLam "y" $ TmBinOp Mult (TmLit (LInt 2)) "y")) `TmApp`
          ("nats" `TmApp` "us" `TmApp` TmLit (LInt 0))

  in Program mainfn [frp_map, frp_nats]

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
    TmLet "fib" fiblam $
    "unfold" `TmApp` "us" `TmApp` TmStable ("fib" `TmApp` "u") `TmApp`
    TmTup (TmLit $ LInt 0) (TmLit $ LInt 1)
 fiblam = TmLam "u" $ TmLam "x" $
          TmLet (PTup "a" "b") "x" $
          TmLet "f" (TmBinOp Add "a" "b") $
          TmTup "f" (TmDelay "u" $ TmTup "b" "f")

prog_unfold :: Program
prog_unfold =
  let mainfn = frp_main (_body frp_fib) (TyStream TyNat)
  in Program mainfn [frp_unfold, frp_nats, frp_fib]

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

prog_swap_fib_nats = Program mainfn [frp_unfold, frp_fib, frp_nats, frp_swap]
  where
    mainfn = frp_main mainbd (TyStream TyNat)
    mainbd =
      TmLam "us" $
      "swap" `TmApp` "us" `TmApp` (TmLit $ LInt 10) `TmApp`
      ("nats" `TmApp` "us" `TmApp` (TmLit $ LInt 0)) `TmApp` ("fib" `TmApp` "us")

main :: IO ()
main = hspec spec

ppdebug :: Pretty p => p -> IO ()
ppdebug = const (return ()) --ppputStrLn

debug :: String -> IO ()
debug = const (return ()) -- putStrLn

spec :: Spec
spec = do
  describe "operational semantics" $ do
    describe "function application" $ do
      it "works with a simple function" $ do
        let term = TmApp (TmLam "x" (TmVar "x")) (TmLit (LInt 10))
        -- ppdebug term
        let r = evalExpr M.empty term
        r `shouldBe` VLit (LInt 10)
      it "works with two arguments" $ do
        let term =
              TmApp
                (TmApp (TmLam "x" (TmLam "y"
                    (TmBinOp Add (TmVar "x") (TmVar "y"))))
                    (TmLit (LInt 10))
                )
                (TmLit (LInt 5))
        -- ppdebug term
        let r = evalExpr M.empty term
        r `shouldBe` VLit (LInt 15)
        -- ppdebug r
      it "adds a nested vars to scope" $ do
        let lam = TmLam "x" (TmLam "y" (TmApp (TmVar "x") (TmVar "y")) )
        let app = TmApp lam (TmLam "z" (TmBinOp Add (TmLit (LInt 10)) (TmVar "z")))
        let term = TmApp app (TmLit (LInt 5))
        -- debug . ppshow $ term
        let r = evalExpr M.empty term
        r `shouldBe` VLit (LInt 15)
        -- debug $ "result: " ++ (ppshow r)
      it "does not capture free variables" $ do
        let l1 = VClosure "x" (TmBinOp Add (TmVar "y") (TmVar "x")) (M.singleton "y" (Right $ VLit (LInt 10)))
        let l2 = TmClosure "y" (TmApp (TmVar "z") (TmVar "y")) (M.singleton "z" (Right l1))
        let term = (TmApp l2 (TmLit (LInt 42)))
        -- ppdebug term
        let r = evalExpr M.empty term
        r `shouldBe` VLit (LInt 52)
        -- debug $ "result: " ++ (ppshow r)
    describe "fixpoint" $ do
      it "works for const" $ do
        let fp = TmApp (TmFix "x" (TmLam "y" (TmVar "y"))) (TmLit $ LInt 10)
        let v = evalExpr M.empty fp
        v `shouldBe` (VLit (LInt 10))
        -- ppdebug v
      it "works for factorial" $ do
        let predn = TmBinOp Sub (TmVar "n") (TmLit $ LInt 1)
        let g    = TmBinOp Eq (TmVar "n") (TmLit $ LInt 1)
        let body = (TmLam "n" (TmITE g (TmLit (LInt 1)) (TmBinOp Mult (TmVar "n") $ TmVar "f" `TmApp` predn)))
        let fact = TmFix "f" body
        -- ppdebug fact
        let v = evalExpr M.empty (fact `TmApp` TmLit (LInt 4))
        v `shouldBe` (VLit (LInt 24))
        -- ppdebug v
      it "works for fibonacci" $ do
        let predn x = TmBinOp Sub (TmVar "n") (TmLit $ LInt x)
        let g       = TmBinOp Leq (TmVar "n") (TmLit $ LInt 1)
        let body = (TmLam "n" (TmITE g (TmVar "n") (TmBinOp Add (TmVar "f" `TmApp` predn 1) $ TmVar "f" `TmApp` predn 2)))
        let fib = TmFix "f" body
        -- ppdebug fib
        let v = evalExpr M.empty (fib `TmApp` TmLit (LInt 7))
        v `shouldBe` (VLit (LInt 13))
        -- ppdebug v

    describe "fixedpoint" $ do
      it "works with stream of allocators" $ do
        let fp = TmFix "xs" $ TmCons TmAlloc (TmDelay TmAlloc (TmVar "xs"))
        let run s e n =
              let (v, s')  = runExpr s M.empty e
                  VCons _ (VPntr l) = v
              in  if n >= 10 then return () else do
                     v `shouldBe` VCons VAlloc (VPntr n)
                     run (tick s') (TmPntrDeref l) (n+1)

        r <- run initialState fp 0
        r `shouldBe` ()

    describe "streams" $ do
      it "works with const" $ do
        let constfn =
              TmLam "us" (TmLam "n" (
                TmLet (PCons (PBind "u") (PDelay "us'")) (TmVar "us") (
                TmLet (PStable (PBind "x")) (TmPromote (TmVar "n")) (
                TmCons (TmVar "x") (TmDelay (TmVar "u")
                  ((TmVar "const") `TmApp` (TmVar "us'") `TmApp` (TmVar "x")))
                ))
              ))
        let mainbd =
              TmLam "us"
              ((TmVar "const") `TmApp` (TmVar "us") `TmApp` (TmLit (LInt 10)))
        let mainfn = Decl undefined "main" mainbd
        let prog = Program mainfn [Decl undefined "const" constfn]
        take 100 (interpProgram prog) `shouldBe` map (VLit . LInt) (replicate 100 10)
        -- debug $ show $ interpProgram prog
      it "works with nats" $ do
        let mainbd =
              TmLam "us"
              ((TmVar "nats") `TmApp` (TmVar "us") `TmApp` (TmLit (LInt 0)))
        let mainfn = frp_main mainbd (TyStream TyNat)
        let prog = Program mainfn [frp_nats]
        take 100 (interpProgram prog) `shouldBe` map (VLit . LInt) [0..99]
      it "works with sum" $ do
        let mainbd = TmLam "us" $
                    (TmVar "sum" `TmApp` TmVar "us") `TmApp` (TmVar "nats" `TmApp` TmVar "us" `TmApp` TmLit (LInt 0))
        let mainfn = frp_main mainbd (TyStream TyNat)
        let prog = Program mainfn [frp_nats, frp_sum_acc, frp_sum]
        take 100 (interpProgram prog) `shouldBe` map (VLit . LInt) (scanl (+) 0 [1..99])

        ppdebug frp_sum_acc
        debug ""
        let (v, s) = evalProgram prog
        debug "===== run 1 ======="
        ppdebug v
        ppdebug s
        let VCons _ (VPntr l) = v
        let (v', s') = runExpr (tick s) M.empty (TmPntrDeref l)
        debug "===== run 2 ======="
        ppdebug v'
        ppdebug s'
        let VCons _ (VPntr l') = v'
        let (v'', s'') = runExpr (tick s') M.empty (TmPntrDeref l')
        debug "===== run 3 ======="
        ppdebug v''
        ppdebug s''
        debug . show $ take 500 (interpProgram prog)
      it "works with tails" $ do

        -- ppdebug frp_tails
        -- debug ""
        let prog = prog_tails
        let k = 10
        let got = take k $ map (take k . toHaskList) (interpProgram prog)
        let expect = map (\n -> map (VLit . LInt) [n..(n+k-1)]) [1..k]
        got `shouldBe` expect

      it "works with map" $ do
        let prog = prog_map
        let k = 100
        let got = take k $ (interpProgram prog)
        -- mapM_ (debug . show) got
        let expect = map (VLit . LInt . (* 2)) [0..k-1]
        got `shouldBe` expect

      it "works with unfold (fib)" $ do
        let prog = prog_unfold
        let k = 50
        let got = take k $ (interpProgram prog)
        -- mapM_ (debug . show) got
        let expect = map (VLit . LInt) $ take k $ unfoldr (\(a,b) -> Just (a+b, (b,a+b))) (0,1)
        got `shouldBe` expect

      it "works with swap 10 nats (fib)" $ do
        let prog = prog_swap_fib_nats
        let k = 50
        let got = take k $ (interpProgram prog)
        -- mapM_ (debug . show) got
        let fibs = unfoldr (\(a,b) -> Just (a+b, (b,a+b))) (0,1)
        let expect = map (VLit . LInt) $ [0..9] ++ take (k-10) (drop 10 fibs)
        got `shouldBe` expect


    describe "tick" $ do
      let mkStore s = EvalState s 0
      it "sats tick [] = []" $ do
        tick initialState `shouldBe` initialState
      it "sats tick [l : v now] = []" $ do
        tick (mkStore M.empty) `shouldBe` initialState
      it "sats tick [l : e later] = [l : v now]" $ do
        let s  = M.singleton 0 $ SVLater (TmLit $ LInt 10) M.empty
        let s' = M.singleton 0 $ SVNow   (VLit  $ LInt 10)
        tick (mkStore $ s) `shouldBe` mkStore s'
      it "sats tick [l1 : v now, l2 : e later] = [l2 : v' now]" $ do
        let s  = M.insert 0 (SVNow (VLit $ LInt 1)) $ M.singleton 1 $ SVLater (TmLit $ LInt 10) M.empty
        let s' = M.singleton 1 $ SVNow  (VLit $ LInt 10)
        tick (mkStore $ s) `shouldBe` mkStore s'
      it "sats tick [0 : e later, 1 : *0 later, 2 : v now] = [0 : v now, 1 : v now]" $ do
        let s  = M.insert 0 (SVLater (TmLit $ LInt 1) M.empty) $ M.insert 1 (SVLater (TmPntrDeref 0) M.empty) $ M.singleton 2 (SVNow (VLit $ LInt 42))
        let s' = M.insert 0 (SVNow (VLit $ LInt 1)) $ M.singleton 1 $ SVNow (VLit $ LInt 1)
        tick (mkStore $ s) `shouldBe` mkStore s'
