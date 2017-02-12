
module FRP.ParserSpec where

import Test.Hspec
import FRP.AST
import FRP.Parser
import FRP.Pretty

import Control.Monad.State
import Debug.Trace
import qualified Data.Map.Strict as M
import Data.List (unfoldr)

import Text.ParserCombinators.Parsec

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  it "should parse lambda expressions" $ do
    parse tmlam "lam" "\\x -> x" `shouldBe` Right (TmLam "x" "x")
    parse expr "lam" "\\x  -> x" `shouldBe` Right (TmLam "x" "x")
    parse expr "lam" "\\x  -> x + x" `shouldBe`
      Right (TmLam "x" ("x" + "x"))

    parse expr "lam" "\\x -> \\y -> x + y" `shouldBe`
      Right (TmLam "x" $ TmLam "y" ("x" + "y"))

  -- it "should parse let expressions" $ do
  --   parse tmlet "let" "let x = 10 in x" `shouldBe`
  --     Right (TmLet "x" 10 "x")
  --   parse expr "let" "let x = 10 in x" `shouldBe`
  --     Right (TmLet "x" 10 "x")
  --   parse expr "let" "let x = y in\n x * y" `shouldBe`
  --     Right (TmLet "x" "y" ("x" * "y"))
  --   parse expr "let" "let x = 10 in let y = 42 in x * y" `shouldBe`
  --     Right (TmLet "x" 10 $ TmLet "y" 42 ("x" * "y"))

  -- it "should parse cons expressions" $ do
  --   parse tmcons "cons" "cons(10, 20)" `shouldBe`
  --     Right (TmCons 10 20)
  --   parse tmcons "cons" "cons ( 10  , 20  )  " `shouldBe`
  --     Right (TmCons 10 20)
  --   parse expr "term" "cons(10, 20)" `shouldBe`
  --     Right (TmCons 10 20)
  --   parse expr "term" "cons ( 10  , 20  )  " `shouldBe`
  --     Right (TmCons 10 20)

  -- it "parses compound expressions" $ do
  --   parse expr "frp" "\\x -> \\y -> let z = x + y in cons(x, z * x + y)" `shouldBe`
  --     Right (TmLam "x" $ TmLam "y" $ TmLet "z" ("x" + "y") $ TmCons "x" ("z" * "x" + "y"))

  -- it "parses application" $ do
  --   parse tmapp "term" "x x" `shouldBe`
  --     Right (TmApp "x" "x")
