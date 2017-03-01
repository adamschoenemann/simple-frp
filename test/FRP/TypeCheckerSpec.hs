{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes       #-}

module FRP.TypeCheckerSpec where

import           FRP.AST
import           FRP.TypeChecker
import           FRP.AST.Construct
import           FRP.Pretty          (ppputStrLn, ppshow)
import           Test.Hspec

import           Control.Monad.State
import           Data.List           (unfoldr)
import qualified Data.Map.Strict     as M
import           Debug.Trace

import           Data.Text           (Text, pack, unpack)
import           NeatInterpolation
import           Text.Parsec         (ParseError, parse)

import           Data.Either         (isRight)
import           FRP.TestFunctions   (frps)


shouldTC :: (Eq (f ()), Show (f ()), Functor f, Show t)
            => Either (TypeErr t) (f a, Qualifier) -> (f (), Qualifier) -> Expectation
shouldTC eith expect = case eith of
  Left err  -> expectationFailure (ppshow err)
  Right (t,q) -> (unitFunc t, q) `shouldBe` expect

shouldTyErr :: Show t => Either (TypeErr t) (Type t, Qualifier) -> Expectation
shouldTyErr = \case
  Left err -> return ()
  Right (t,q) -> expectationFailure $ show (t, q)

main :: IO ()
main = hspec spec
spec :: Spec
spec = do
  describe "typechecker" $ do
    describe "simple types" $ do
      it "works with nat" $ do
        runCheckTerm' (tmint 1) `shouldTC` (tynat, QNow)
    describe "let exprs" $ do
      it "works for let x = x in x" $ do
        let ctx = (Ctx (M.singleton "x" (tynat, QNow)))
        runCheckTerm ctx (tmlet "x" "x" "x") `shouldTC` (tynat, QNow)
      it "works for let y = x in x" $ do
        let ctx = (Ctx (M.singleton "x" (tynat, QNow)))
        runCheckTerm ctx (tmlet "y" "x" "x") `shouldTC` (tynat, QNow)
    describe "tuples" $ do
      it "works for fst (10,True)" $ do
        runCheckTerm' (tmfst (tmtup 10 10)) `shouldTC` (tynat, QNow)
      it "works for snd (10,False)" $ do
        runCheckTerm' (tmsnd (tmtup 10 (tmbool False))) `shouldTC` (tybool, QNow)
    describe "binops" $ do
      it "works for Add" $ do
        runCheckTerm' (tmbinop Add 1 1) `shouldTC` (tynat, QNow)
      it "works for Sub" $ do
        runCheckTerm' (tmbinop Sub 10 1) `shouldTC` (tynat, QNow)
      it "works for Eq" $ do
        runCheckTerm' (tmbinop Eq 10 1) `shouldTC` (tybool, QNow)
      it "works with nested" $ do
        runCheckTerm' (tmbinop Eq (5 + 5) (20 - 10)) `shouldTC` (tybool, QNow)
      it "errs with wrong args" $ do
        shouldTyErr (runCheckTerm' (tmbinop Add 1 (tmbool True)))
    describe "lambdas" $ do
      it "works for \\(x:Nat) -> x"  $ do
        runCheckTerm' (tmlamty "x" (tynat) "x") `shouldTC`
          (tynat |-> tynat, QNow)
      it "works for \\(x:Nat) -> x * x"  $ do
        runCheckTerm' (tmlamty "x" (tynat) ("x" * "x")) `shouldTC`
          (tynat |-> tynat, QNow)
      it "works for \\(x:Nat) -> x == x"  $ do
        runCheckTerm' (tmlamty "x" (tynat) ("x" `eq` "x")) `shouldTC`
          (tynat |-> tybool, QNow)
      it "works for \\(x:Nat) (y:Nat) -> x == y"  $ do
        runCheckTerm'
          (tmlamty "x" tynat
            (tmlamty "y" tynat $ "x" `eq` "x")) `shouldTC`
          (tynat |-> tynat |-> tybool, QNow)
      it "works for \\(xs: @(S Nat)) (x:Nat) -> cons(x,xs)" $ do
        runCheckTerm' (tmlamty "xs" ((tystream tynat)) $
                       tmlamty "x" tynat $ tmcons "x" "xs")
          `shouldTC` ((tylater $ tystream tynat) |-> tynat |-> tystream tynat, QNow)
