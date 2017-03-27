{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes       #-}

module FRP.TypeInferenceSpec where

import           FRP.AST
import           FRP.TypeInference
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
import           FRP.TestFunctions
import           Data.List            (intercalate)
import           FRP.Parser.Decl
import           Text.Parsec
import           FRP.AST.QuasiQuoter

main :: IO ()
main = hspec spec

shouldInfer :: (Eq (f ()), Show (f ()), Functor f, Show t, Eq t)
            => Either (TyExcept t) ((f a, Qualifier), [Constraint t])
            -> (f (), Qualifier, [Constraint ()])
            -> Expectation
shouldInfer eith expect = case eith of
  Left err  -> expectationFailure (ppshow err)
  Right ((t,q), cs) -> (unitFunc t, q, fmap unitFunc cs) `shouldBe` expect

shouldTyErr :: Show t => Either (TyExcept t) (Type t, Qualifier) -> Expectation
shouldTyErr = \case
  Left err -> return ()
  Right (t,q) -> expectationFailure $ show (t, q)

shouldSolve :: Either (TyExcept t) (Scheme t, Qualifier)
            -> (Scheme (), Qualifier)
            -> Expectation
shouldSolve eith expect = case eith of
  Left err  -> expectationFailure (ppshow err)
  Right (sc, q) -> (unitFunc sc, q) `shouldBe` expect

spec :: Spec
spec = do
  describe "typeinference" $ do
    describe "simple terms" $ do
      it "should infer \\x -> x" $ do
       runInfer' (infer [term|\x -> x|]) `shouldInfer`
        ("a" |-> "a", QNow, [])
      it "should infer \\x -> 10" $ do
       runInfer' (infer [term|\x -> 10|]) `shouldInfer`
        ("a" |-> tynat, QNow, [])
      it "should infer \\x -> True" $ do
       runInfer' (infer [term|\x -> True|]) `shouldInfer`
        ("a" |-> tybool, QNow, [])
      it "should infer \\x y -> y" $ do
       runInfer' (infer [term|\x y -> y|]) `shouldInfer`
        ("a" |-> "b" |-> "b", QNow, [])
      it "should infer \\x y -> x" $ do
       runInfer' (infer [term|\x y -> x|]) `shouldInfer`
        ("a" |-> "b" |-> "a", QNow, [])
      it "should infer \\x y -> x" $ do
       runInfer' (infer [term|\x y -> x|]) `shouldInfer`
        ("a" |-> "b" |-> "a", QNow, [])
      it "should infer \\f x -> f x" $ do
       runInfer' (infer [term|\f x -> f x|]) `shouldInfer`
        ("a" |-> "b" |-> "c", QNow, [("a" .=. "b" |-> "c")])
      it "should infer \\f g x -> f (g x)" $ do
       runInfer' (infer [term|\f g x -> f (g x)|]) `shouldInfer`
        ("a" |-> "b" |-> "c" |-> "e", QNow,
          [("b" .=. "c" |-> "d"), ("a" .=. "d" |-> "e")]
        )
    describe "binary ops" $ do
      it "should infer 10 + 10" $ do
       runInfer' (infer [term|10 + 10|]) `shouldInfer`
        ("a", QNow, [tynat |-> tynat |-> "a" .=. tynat |-> tynat |-> tynat])
      it "should infer \\x y z -> x + y == z : Nat -> Nat -> Nat -> Bool" $ do
        runInfer' (infer [term|\x y z -> x + y == z|]) `shouldInfer`
          ( "a" |-> "b" |-> "c" |-> "e"
          , QNow
          , [ "a" |-> "b" |-> "d" .=. tynat |-> tynat |-> tynat
            , "d" |-> "c" |-> "e" .=. tynat |-> tynat |-> tybool
            ]
          )

        inferTerm' [term|\x y z -> x + y == z|] `shouldSolve`
          (toScheme $ tynat |-> tynat |-> tynat |-> tybool, QNow)

      it "should infer \\f x -> f (x + 1) + 1 : (Nat -> Nat) -> Nat -> Nat" $ do
        inferTerm' [term|\f x -> f (x + 1) + 1|] `shouldSolve`
          (toScheme $ (tynat |-> tynat) |-> tynat |-> tynat, QNow)

      it "should infer \\f x -> f (x + 1) && True : (Nat -> Bool) -> Nat -> Bool" $ do
        inferTerm' [term|\f x -> f (x + 1) && True |] `shouldSolve`
          (toScheme $ (tynat |-> tybool) |-> tynat |-> tybool, QNow)

    describe "if-then-else" $ do
      it "\\x -> if x > 10 then x else x * 2 : Nat -> Nat" $ do
        inferTerm' [term|\x -> if x > 10 then x else x * 2 |] `shouldSolve`
          (toScheme $ tynat |-> tynat, QNow)
      it "\\f x -> if f x then f 10 else False : (Nat -> Bool) -> Nat -> Bool" $ do
        inferTerm' [term|\f x -> if f x then f 10 else False|] `shouldSolve`
          (toScheme $ (tynat |-> tybool) |-> tynat |-> tybool, QNow)



