
module FRP.SemanticsSpec where

import Test.Hspec
import FRP.AST
import FRP.Semantics
import FRP.Pretty

import Control.Monad.State
import Debug.Trace
import qualified Data.Map.Strict as M
import Data.List (unfoldr)

import FRP.TestFunctions
import FRP.TestPrograms

main :: IO ()
main = hspec spec

ppdebug :: Pretty p => p -> IO ()
-- ppdebug = ppputStrLn
ppdebug = const (return ())

debug :: String -> IO ()
-- debug = putStrLn
debug = const (return ())

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
