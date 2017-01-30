
module FRP.SemanticsSpec where

import Test.Hspec
import FRP.AST
import FRP.Semantics
import FRP.Pretty

import Control.Monad.State
import Debug.Trace
import qualified Data.Map.Strict as M


main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  describe "operational semantics" $ do
    describe "function application" $ do
      it "works with a simple function" $ do
        let term = TmApp (TmLam "x" (TmVar "x")) (TmLit (LInt 10))
        ppputStrLn term
        let r = evalExpr M.empty term
        ppputStrLn r
      it "works with two arguments" $ do
        let term =
              TmApp
                (TmApp (TmLam "x" (TmLam "y"
                    (TmBinOp Add (TmVar "x") (TmVar "y"))))
                    (TmLit (LInt 10))
                )
                (TmLit (LInt 5))
        ppputStrLn term
        let r = evalExpr M.empty term
        ppputStrLn r
      it "adds a nested vars to scope" $ do
        let lam = TmLam "x" (TmLam "y" (TmApp (TmVar "x") (TmVar "y")) )
        let app = TmApp lam (TmLam "z" (TmBinOp Add (TmLit (LInt 10)) (TmVar "z")))
        let term = TmApp app (TmLit (LInt 5))
        putStrLn . ppshow $ term
        let r = evalExpr M.empty term
        putStrLn $ "result: " ++ (ppshow r)
      it "does not capture free variables" $ do
        let l1 = VClosure "x" (TmBinOp Add (TmVar "y") (TmVar "x")) (M.singleton "y" (Right $ VLit (LInt 10)))
        let l2 = TmClosure "y" (TmApp (TmVar "z") (TmVar "y")) (M.singleton "z" (Right l1))
        let term = (TmApp l2 (TmLit (LInt 42)))
        ppputStrLn term
        let r = evalExpr M.empty term
        putStrLn $ "result: " ++ (ppshow r)
    describe "fixpoint" $ do
      it "works for const" $ do
        let fp = TmApp (TmFix "x" (TmLam "y" (TmVar "y"))) (TmLit $ LInt 10)
        let v = evalExpr M.empty fp
        v `shouldBe` (VLit (LInt 10))
        ppputStrLn v
      it "works for factorial" $ do
        let predn = TmBinOp Sub (TmVar "n") (TmLit $ LInt 1)
        let g    = TmBinOp Eq (TmVar "n") (TmLit $ LInt 1)
        let body = (TmLam "n" (TmITE g (TmLit (LInt 1)) (TmBinOp Mult (TmVar "n") $ TmVar "f" `TmApp` predn)))
        let fact = TmFix "f" body
        ppputStrLn fact
        let v = evalExpr M.empty (fact `TmApp` TmLit (LInt 4))
        -- v `shouldBe` (VLit (LInt 24))
        ppputStrLn v
      it "works for fibonacci" $ do
        let predn x = TmBinOp Sub (TmVar "n") (TmLit $ LInt x)
        let g       = TmBinOp Leq (TmVar "n") (TmLit $ LInt 1)
        let body = (TmLam "n" (TmITE g (TmVar "n") (TmBinOp Add (TmVar "f" `TmApp` predn 1) $ TmVar "f" `TmApp` predn 2)))
        let fib = TmFix "f" body
        ppputStrLn fib
        let v = evalExpr M.empty (fib `TmApp` TmLit (LInt 7))
        v `shouldBe` (VLit (LInt 13))
        ppputStrLn v

    describe "streams" $ do
      it "works with const" $ do
        let constfn =
              TmLam "us" (TmLam "n" (
                TmLet (PCons (PBind "u") (PDelay (PBind "us'"))) (TmVar "us") (
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
        ppputStrLn constfn
        let rs = runProgram prog
        putStrLn $ "result 1:\n" ++ (show rs)
        -- let VCons x (VPntr l) = v
        -- evalExpr ()

    describe "tick" $ do
      let mkStore s = EvalState s 0
      it "sats tick [] = []" $ do
        tick initialState `shouldBe` initialState
      it "sats tick [l : v now] = []" $ do
        tick (mkStore M.empty) `shouldBe` initialState
      it "sats tick [l : e later] = [l : v now]" $ do
        let s  = M.singleton 0 $ SVLater (TmLit $ LInt 10) M.empty
        let s' = M.singleton 0 $ SVNow   (VLit  $ LInt 10) M.empty
        tick (mkStore $ s) `shouldBe` mkStore s'