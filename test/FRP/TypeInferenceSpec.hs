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

shouldTyErr :: Show t => Either e (QualSchm t) -> Expectation
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

    describe "cons" $ do
      it "\\x xs -> cons(x,xs) : a -> @(S a) -> S a" $ do
        inferTerm' [term|\x xs -> cons(x,xs) |] `shouldSolve`
          (Forall ["a"] ("a" |-> tylater (tystream "a") |-> tystream "a"), QNow)

      it "\\f x xs -> cons(f x, xs) : (a -> b) -> a -> @(S b) -> S b" $ do
        inferTerm' [term|\f x xs -> cons(f x,xs) |] `shouldSolve`
          (Forall ["a", "b"]
             (("a" |-> "b") |-> "a" |-> tylater (tystream "b") |-> tystream "b")
          , QNow)

    describe "fst" $ do
      it "\\x -> fst x"  $ do
        inferTerm' [term|\x -> fst x|] `shouldSolve`
          (Forall ["a", "b"] $ "a" .*. "b" |-> "a", QNow)

      it "\\x -> (fst x) * 2"  $ do
        inferTerm' [term|\x -> (fst x) * 2|] `shouldSolve`
          (Forall ["a"] $ tynat .*. "a" |-> tynat, QNow)

      it "\\x -> fst x * 2"  $ do
        inferTerm' [term|\x -> fst x * 2|] `shouldSolve`
          (Forall ["a"] $ tynat .*. "a" |-> tynat, QNow)

    describe "snd" $ do
      it "\\x -> snd x"  $ do
        inferTerm' [term|\x -> snd x|] `shouldSolve`
          (Forall ["a", "b"] $ "a" .*. "b" |-> "b", QNow)

      it "\\x -> (snd x) * 2"  $ do
        inferTerm' [term|\x -> (snd x) * 2|] `shouldSolve`
          (Forall ["a"] $ "a" .*. tynat |-> tynat, QNow)

      it "\\x -> snd x * 2"  $ do
        inferTerm' [term|\x -> snd x * 2|] `shouldSolve`
          (Forall ["a"] $ "a" .*. tynat |-> tynat, QNow)

    describe "tuples" $ do
      it "\\x y -> (x,y) : a -> b -> a * b"  $ do
        inferTerm' [term|\x y -> (x,y)|] `shouldSolve`
          (Forall ["a","b"] $ "a" |-> "b" |-> "a" .*. "b", QNow)

      it "\\x y -> (x * 2,y) : Nat -> a -> a * b"  $ do
        inferTerm' [term|\x y -> (x * 2,y)|] `shouldSolve`
          (Forall ["a"] $ tynat |-> "a" |-> tynat .*. "a", QNow)

      it "\\x y -> (x,y * 2) : a -> Nat -> a * Nat"  $ do
        inferTerm' [term|\x y -> (x,y * 2)|] `shouldSolve`
          (Forall ["a"] $ "a" |-> tynat |-> "a" .*. tynat, QNow)

    describe "let-generalization" $ do
      it "let f = (\\x -> x) in let g = (f True) in f 3" $ do
        inferTerm' [term|let f = (\x -> x) in let g = (f True) in f 3|] `shouldSolve`
          (toScheme tynat, QNow)

    describe "delay-elim" $ do
      it "\\u x -> let delay(x') = x in delay(u,x')" $ do
        inferTerm' [term|\u x -> let delay(x') = x in delay(u,x')|] `shouldSolve`
          (Forall ["a"] $ tyalloc |-> tylater "a" |-> tylater "a", QNow)

    describe "cons-elim" $ do
      it "\\xs -> let cons(x, xs') = xs in x" $ do
        let trm = [term|\xs -> let cons(x, xs') = xs in x|]
        inferTerm' trm `shouldSolve`
          (Forall ["a"] $ tystream "a" |-> "a", QNow)

      it "\\u xs -> let cons(x, delay(xs')) = xs in delay(u, xs')" $ do
        let trm = [term|\u xs -> let cons(x, delay(xs')) = xs in delay(u,xs')|]
        inferTerm' trm `shouldSolve`
          (Forall ["a"] $ tyalloc |-> tystream "a" |-> tylater (tystream "a"), QNow)

      it "fails \\xs -> let cons(x, delay(xs')) = xs in let y = x True in x 10" $ do
        let trm = [term|\xs -> let cons(x, delay(xs')) = xs in let y = x True in x 10|]
        shouldTyErr (inferTerm' trm )

    describe "tuple-elim" $ do
      it "\\c -> let (a,b) = c in a" $ do
        let trm = [term|\c -> let (a,b) = c in a|]
        inferTerm' trm `shouldSolve`
          (Forall ["a", "b"] $ "a" .*. "b" |-> "a", QNow)

      it "\\c -> let (a,b) = c in b" $ do
        let trm = [term|\c -> let (a,b) = c in b|]
        inferTerm' trm `shouldSolve`
          (Forall ["a", "b"] $ "a" .*. "b" |-> "b", QNow)

      it "\\c -> let (a,b) = c in a b" $ do
        let trm = [term|\c -> let (a,b) = c in a b|]
        inferTerm' trm `shouldSolve`
          (Forall ["a", "b"] $ ("a" |-> "b") .*. "a" |-> "b", QNow)

      it "\\c -> let (a,b) = c in let x = a 10 in a b" $ do
        let trm = [term|\c -> let (a,b) = c in let x = a 10 in a b|]
        inferTerm' trm `shouldSolve`
          (Forall ["a"] $ (tynat |-> "a") .*. tynat |-> "a", QNow)

      it "fails \\c -> let (a,b) = c in let x = a 10 in a True" $ do
        let trm = [term|\c -> let (a,b) = c in let x = a 10 in a True|]
        shouldTyErr (inferTerm' trm)

    describe "fixpoint" $ do
      it "fix f. 10 : Nat" $ do
        inferTerm' [term|fix f. 10|] `shouldSolve`
          (toScheme $ tynat, QNow)

      it "fix f. \\x -> 10 : a -> Nat" $ do
        inferTerm' [term|fix f. \x -> 10|] `shouldSolve`
          (Forall ["a"] $ "a" |-> tynat, QNow)

      it "fix f. \\x y -> 10 : a -> Nat" $ do
        inferTerm' [term|fix f. \x -> 10|] `shouldSolve`
          (Forall ["a"] $ "a" |-> tynat, QNow)

      -- it "fix f. \\x y -> f x y : a -> b -> c" $ do
      --   inferTerm' [term|fix f. \x y -> f x y|] `shouldSolve`
      --     (Forall ["b","c","e"] $ "b" |-> "c" |-> "e", QNow)

  describe "test functions" $ do
    it "works for const" $ do
      inferTerm' (_body frp_const) `shouldSolve`
        (Forall ["a"] $ tystream tyalloc |-> "a" |-> tystream "a", QNow)

    it "works for const_fix" $ do
      inferTerm' (_body frp_const_fix) `shouldSolve`
        (Forall ["a"] $ tystream tyalloc |-> "a" |-> tystream "a", QNow)

    it "works for nats" $ do
      inferTerm' (_body frp_nats) `shouldSolve`
        (Forall [] $ tystream tyalloc |-> tynat |-> tystream tynat, QNow)

    it "works for map" $ do
      inferTerm' (_body frp_map) `shouldSolve`
        (Forall ["a","b"] $ tystream tyalloc
                        |-> tystable ("a" |-> "b")
                        |-> tystream "a"
                        |-> tystream "b", QNow)

    it "works for tails" $ do
      inferTerm' (_body frp_tails) `shouldSolve`
        (Forall ["a"] $ tystream tyalloc
                        |-> tystream "a"
                        |-> tystream (tystream "a"), QNow)

    it "works for sum_acc" $ do
      inferTerm' (_body frp_sum_acc) `shouldSolve`
        (toScheme $ tystream tyalloc
                  |-> tystream tynat
                  |-> tynat
                  |-> tystream tynat, QNow)

    it "works for unfold" $ do
      inferTerm' (_body frp_unfold) `shouldSolve`
        (Forall ["a","b"]
          $   tystream tyalloc
          |-> tystable ("a" |-> "b" .*. tylater "a")
          |-> "a"
          |-> tystream "b", QNow)

    it "works for swap" $ do
      inferTerm' (_body frp_swap) `shouldSolve`
        (Forall ["a"]
          $   tystream tyalloc
          |-> tynat
          |-> tystream "a"
          |-> tystream "a"
          |-> tystream "a", QNow)



