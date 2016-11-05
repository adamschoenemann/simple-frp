
module FRP.SemanticsSpec where

import Test.Hspec
import FRP.AST
import FRP.Semantics
import FRP.Pretty

import Control.Monad.State
import Debug.Trace


main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  describe "operationional semantics" $ do
    describe "function application" $ do
      it "works with a simple function" $ do
        let term = TmApp (TmLam "x" (TmVar "x")) (TmLit (LInt 10))
        let (r, s) = runEvalInit $ evalStep term
        -- r `shouldBe`
        ppputStrLn r
      it "adds a nested vars to scope" $ do
        let lam = TmLam "x" (TmLam "y" (TmApp (TmVar "x") (TmVar "y")) )
        let app = TmApp lam (TmLam "z" (TmBinOp Add (TmLit (LInt 10)) (TmVar "z")))
        let term = TmApp app (TmLit (LInt 5))
        putStrLn . ppshow $ term
        let (r, rs) = runEvalInit $ evalStep term
        -- let (r, rs) = runEvalInit $ evalStep app
        -- let (r', rs') = runE
        putStrLn . ppshow $ r
        putStrLn $ show rs
