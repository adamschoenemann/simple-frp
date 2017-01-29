
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
  describe "operationional semantics" $ do
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
        let l1 = VClosure "x" (TmBinOp Add (TmVar "y") (TmVar "x")) (M.singleton "y" (VLit (LInt 10)))
        let l2 = TmClosure "y" (TmApp (TmVar "z") (TmVar "y")) (M.singleton "z" l1)
        let term = (TmApp l2 (TmLit (LInt 42)))
        ppputStrLn term
        let r = evalExpr M.empty term
        putStrLn $ "result: " ++ (ppshow r)
    describe "streams" $ do
      it "works just a little bit" $ do
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
        let v = evalProgram prog
        putStrLn $ "result:\n" ++ (ppshow v)
