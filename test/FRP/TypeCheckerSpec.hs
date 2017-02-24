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
  Left err  -> expectationFailure (show err)
  Right (t,q) -> (unitFunc t, q) `shouldBe` expect

main :: IO ()
main = hspec spec
spec :: Spec
spec = do
  describe "typechecker" $ do
    describe "simple types" $ do
      it "works with nat" $ do
        runCheckTerm' (tmlit (LInt 1)) `shouldTC` (TyNat (), QNow)
    describe "let exprs" $ do
      it "works for let x = x in x" $ do
        let ctx = (Ctx (M.singleton "x" (TyNat (), QNow)))
        runCheckTerm ctx (tmlet "x" "x" "x") `shouldTC` (TyNat (), QNow)
      it "works for let y = x in x" $ do
        let ctx = (Ctx (M.singleton "x" (TyNat (), QNow)))
        runCheckTerm ctx (tmlet "y" "x" "x") `shouldTC` (TyNat (), QNow)
    describe "tuples" $ do
      it "works for fst (10,True)" $ do
        runCheckTerm' (tmfst (tmtup 10 10)) `shouldTC` (TyNat (), QNow)
      it "works for snd (10,False)" $ do
        runCheckTerm' (tmsnd (tmtup 10 (tmlit $ LBool False))) `shouldTC` (TyBool (), QNow)
