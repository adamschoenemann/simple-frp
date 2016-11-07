
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
        let r = evalExpr M.empty term
        -- r `shouldBe`
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
        -- let (r, rs) = runEvalInit $ evalStep app
        -- let (r', rs') = runE
        putStrLn $ "result: " ++ (ppshow r)
        -- putStrLn $ show rs
