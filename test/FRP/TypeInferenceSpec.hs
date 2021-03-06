{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes       #-}

module FRP.TypeInferenceSpec where

import           FRP.AST
import           FRP.TypeInference
import           FRP.AST.Construct
import           FRP.Pretty          (ppputStrLn, ppshow, Pretty)
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
import           Text.Parsec
import           FRP.AST.QuasiQuoter

main :: IO ()
main = hspec spec

shouldInfer :: (Eq (f ()), Show (f ()), Functor f, Show t, Pretty t, Eq t)
            => Either (TyExcept t) (f a, InferWrite t)
            -> (f (), [Constraint ()])
            -> Expectation
shouldInfer eith expect = case eith of
  Left err  -> expectationFailure (show err)
  Right (t, (cs, stbls)) -> (unitFunc t, fmap unitFunc cs) `shouldBe` expect

shouldTyErr :: Show t => Either e (Scheme t) -> Expectation
shouldTyErr = \case
  Left err -> return ()
  Right t -> expectationFailure $ show t

shouldSolve :: Pretty t => Either (TyExcept t) (Scheme t)
            -> Scheme ()
            -> Expectation
shouldSolve eith expect = case eith of
  Left err  -> expectationFailure (ppshow err)
  Right sc -> unitFunc sc `shouldBe` expect

spec :: Spec
spec = do
  describe "typeinference" $ do
    describe "simple terms" $ do
      it "should infer \\x -> x" $ do
       runInfer' (infer [unsafeTerm|\x -> x|]) `shouldInfer`
        ("0a" |-> "0a", [])
      it "should infer \\x -> 10" $ do
       runInfer' (infer [unsafeTerm|\x -> 10|]) `shouldInfer`
        ("0a" |-> tynat, [])
      it "should infer \\x -> True" $ do
       runInfer' (infer [unsafeTerm|\x -> True|]) `shouldInfer`
        ("0a" |-> tybool, [])
      it "should infer \\x y -> y" $ do
       runInfer' (infer [unsafeTerm|\x y -> y|]) `shouldInfer`
        ("0a" |-> "0b" |-> "0b", [])
      it "should infer \\x y -> x" $ do
       runInfer' (infer [unsafeTerm|\x y -> x|]) `shouldInfer`
        ("0a" |-> "0b" |-> "0a", [])
      it "should infer \\x y -> x" $ do
       runInfer' (infer [unsafeTerm|\x y -> x|]) `shouldInfer`
        ("0a" |-> "0b" |-> "0a", [])
      it "should infer \\f x -> f x" $ do
       runInfer' (infer [unsafeTerm|\f x -> f x|]) `shouldInfer`
        ("0a" |-> "0b" |-> "0c", [("0a" .=. "0b" |-> "0c")])
      it "should infer \\f g x -> f (g x)" $ do
       runInfer' (infer [unsafeTerm|\f g x -> f (g x)|]) `shouldInfer`
        ("0a" |-> "0b" |-> "0c" |-> "0e",
          [("0b" .=. "0c" |-> "0d"), ("0a" .=. "0d" |-> "0e")]
        )
    describe "binary ops" $ do
      it "should infer 10 + 10" $ do
       runInfer' (infer [unsafeTerm|10 + 10|]) `shouldInfer`
        (tynat, [tynat .=. tynat, tynat .=. tynat])

      it "should infer \\x y z -> x + y == z : Nat -> Nat -> Nat -> Bool" $ do
        inferTerm' [unsafeTerm|\x y z -> x + y == z|] `shouldSolve`
          (toScheme $ tynat |-> tynat |-> tynat |-> tybool)

        inferTerm' [unsafeTerm|\x y z -> x + y == z|] `shouldSolve`
          (toScheme $ tynat |-> tynat |-> tynat |-> tybool)

      it "should infer \\f x -> f (x + 1) + 1 : (Nat -> Nat) -> Nat -> Nat" $ do
        inferTerm' [unsafeTerm|\f x -> f (x + 1) + 1|] `shouldSolve`
          (toScheme $ (tynat |-> tynat) |-> tynat |-> tynat)

      it "should infer \\f x -> f (x + 1) && True : (Nat -> Bool) -> Nat -> Bool" $ do
        inferTerm' [unsafeTerm|\f x -> f (x + 1) && True |] `shouldSolve`
          (toScheme $ (tynat |-> tybool) |-> tynat |-> tybool)

    describe "if-then-else" $ do
      it "\\x -> if x > 10 then x else x * 2 : Nat -> Nat" $ do
        inferTerm' [unsafeTerm|\x -> if x > 10 then x else x * 2 |] `shouldSolve`
          (toScheme $ tynat |-> tynat)
      it "\\f x -> if f x then f 10 else False : (Nat -> Bool) -> Nat -> Bool" $ do
        inferTerm' [unsafeTerm|\f x -> if f x then f 10 else False|] `shouldSolve`
          (toScheme $ (tynat |-> tybool) |-> tynat |-> tybool)

    describe "cons" $ do
      it "\\x xs -> cons(x,xs) : a -> @(S a) -> S a" $ do
        inferTerm' [unsafeTerm|\x xs -> cons(x,xs) |] `shouldSolve`
          (Forall ["0a"] ("0a" |-> tylater (tystream "0a") |-> tystream "0a"))

      it "\\f x xs -> cons(f x, xs) : (a -> b) -> a -> @(S b) -> S b" $ do
        inferTerm' [unsafeTerm|\f x xs -> cons(f x,xs) |] `shouldSolve`
          (Forall ["0a", "0b"]
             (("0a" |-> "0b") |-> "0a" |-> tylater (tystream "0b") |-> tystream "0b")
          )

    describe "fst" $ do
      it "\\x -> fst x"  $ do
        inferTerm' [unsafeTerm|\x -> fst x|] `shouldSolve`
          (Forall ["0a", "0b"] $ "0a" .*. "0b" |-> "0a")

      it "\\x -> (fst x) * 2"  $ do
        inferTerm' [unsafeTerm|\x -> (fst x) * 2|] `shouldSolve`
          (Forall ["0a"] $ tynat .*. "0a" |-> tynat)

      it "\\x -> fst x * 2"  $ do
        inferTerm' [unsafeTerm|\x -> fst x * 2|] `shouldSolve`
          (Forall ["0a"] $ tynat .*. "0a" |-> tynat)

    describe "snd" $ do
      it "\\x -> snd x"  $ do
        inferTerm' [unsafeTerm|\x -> snd x|] `shouldSolve`
          (Forall ["0a", "0b"] $ "0a" .*. "0b" |-> "0b")

      it "\\x -> (snd x) * 2"  $ do
        inferTerm' [unsafeTerm|\x -> (snd x) * 2|] `shouldSolve`
          (Forall ["0a"] $ "0a" .*. tynat |-> tynat)

      it "\\x -> snd x * 2"  $ do
        inferTerm' [unsafeTerm|\x -> snd x * 2|] `shouldSolve`
          (Forall ["0a"] $ "0a" .*. tynat |-> tynat)

    describe "tuples" $ do
      it "\\x y -> (x,y) : a -> b -> a * b"  $ do
        inferTerm' [unsafeTerm|\x y -> (x,y)|] `shouldSolve`
          (Forall ["0a","0b"] $ "0a" |-> "0b" |-> "0a" .*. "0b")

      it "\\x y -> (x * 2,y) : Nat -> a -> a * b"  $ do
        inferTerm' [unsafeTerm|\x y -> (x * 2,y)|] `shouldSolve`
          (Forall ["0a"] $ tynat |-> "0a" |-> tynat .*. "0a")

      it "\\x y -> (x,y * 2) : a -> Nat -> a * Nat"  $ do
        inferTerm' [unsafeTerm|\x y -> (x,y * 2)|] `shouldSolve`
          (Forall ["0a"] $ "0a" |-> tynat |-> "0a" .*. tynat)

      it "\\y f -> f y + f (10, 20)"  $ do
        inferTerm' [unsafeTerm|\y f -> f y + f (10, 20)|] `shouldSolve`
          (toScheme $ tynat .*. tynat |-> (tynat .*. tynat |-> tynat) |-> tynat)

    -- describe "let-generalization" $ do
    --   it "let f = (\\x -> x) in let g = (f True) in f 3" $ do
    --     inferTerm' [unsafeTerm|let f = (\x -> x) in let g = (f True) in f 3|] `shouldSolve`
    --       (toScheme tynat)

    describe "sum-types" $ do

      describe "inl" $ do
        it "\\x -> inl x" $ do
          inferTerm' [unsafeTerm|\x -> inl x|] `shouldSolve`
            (Forall ["0a", "0b"] $ "0a" |-> "0a" .+. "0b")

        it "inl 10" $ do
          inferTerm' [unsafeTerm|inl 10|] `shouldSolve`
            (Forall ["0a"] $ tynat .+. "0a")

        it "\\f -> f (inl 10) && False" $ do
          inferTerm' [unsafeTerm|\f -> f (inl 10) && False|] `shouldSolve`
            (Forall ["0a"] $ (tynat .+. "0a" |-> tybool) |-> tybool)

      describe "inr" $ do
        it "\\x -> inr x" $ do
          inferTerm' [unsafeTerm|\x -> inr x|] `shouldSolve`
            (Forall ["0a", "0b"] $ "0a" |-> "0b" .+. "0a")

        it "inr 10" $ do
          inferTerm' [unsafeTerm|inr 10|] `shouldSolve`
            (Forall ["0a"] $ "0a" .+. tynat)

        it "\\f -> f (inr 10) && False" $ do
          inferTerm' [unsafeTerm|\f -> f (inr 10) && False|] `shouldSolve`
            (Forall ["0a"] $ ("0a" .+. tynat |-> tybool) |-> tybool)

      describe "case" $ do
        let t1 = [unsafeTerm|\x -> case x of | inl y -> y < 20 | inr z -> z && False|]
        it (ppshow t1) $ do
          inferTerm' t1 `shouldSolve`
            (Forall [] $ tynat .+. tybool |-> tybool)

        let t2 = [unsafeTerm|\x xx -> case x of | inl y -> xx | inr z -> xx|]
        it (ppshow t2) $ do
          inferTerm' t2 `shouldSolve`
            (Forall ["0a","0b","0c"] $ "0b" .+. "0c" |-> "0a" |-> "0a")

        let t3 = [unsafeTerm|\x -> case x of | inl y -> y | inr z -> z|]
        it (ppshow t3) $ do
          inferTerm' t3 `shouldSolve`
            (Forall ["0a"] $ "0a" .+. "0a" |-> "0a")

    describe "delay-elim" $ do
      it "\\u x -> let delay(x') = x in delay(u,x')" $ do
        inferTerm' [unsafeTerm|\u x -> let delay(x') = x in delay(u,x')|] `shouldSolve`
          (Forall ["0a"] $ tyalloc |-> tylater "0a" |-> tylater "0a")

    describe "cons-elim" $ do
      it "\\xs -> let cons(x, xs') = xs in x" $ do
        let trm = [unsafeTerm|\xs -> let cons(x, xs') = xs in x|]
        inferTerm' trm `shouldSolve`
          (Forall ["0a"] $ tystream "0a" |-> "0a")

      it "\\u xs -> let cons(x, delay(xs')) = xs in delay(u, xs')" $ do
        let trm = [unsafeTerm|\u xs -> let cons(x, delay(xs')) = xs in delay(u,xs')|]
        inferTerm' trm `shouldSolve`
          (Forall ["0a"] $ tyalloc |-> tystream "0a" |-> tylater (tystream "0a"))

      it "fails \\xs -> let cons(x, delay(xs')) = xs in let y = x True in x 10" $ do
        let trm = [unsafeTerm|\xs -> let cons(x, delay(xs')) = xs in let y = x True in x 10|]
        shouldTyErr (inferTerm' trm )

    describe "tuple-elim" $ do
      it "\\c -> let (a,b) = c in a" $ do
        let trm = [unsafeTerm|\c -> let (a,b) = c in a|]
        inferTerm' trm `shouldSolve`
          (Forall ["0a", "0b"] $ "0a" .*. "0b" |-> "0a")

      it "\\c -> let (a,b) = c in b" $ do
        let trm = [unsafeTerm|\c -> let (a,b) = c in b|]
        inferTerm' trm `shouldSolve`
          (Forall ["0a", "0b"] $ "0a" .*. "0b" |-> "0b")

      it "\\c -> let (a,b) = c in a b" $ do
        let trm = [unsafeTerm|\c -> let (a,b) = c in a b|]
        inferTerm' trm `shouldSolve`
          (Forall ["0a", "0b"] $ ("0a" |-> "0b") .*. "0a" |-> "0b")

      it "\\c -> let (a,b) = c in let x = a 10 in a b" $ do
        let trm = [unsafeTerm|\c -> let (a,b) = c in let x = a 10 in a b|]
        inferTerm' trm `shouldSolve`
          (Forall ["0a"] $ (tynat |-> "0a") .*. tynat |-> "0a")

      it "fails \\c -> let (a,b) = c in let x = a 10 in a True" $ do
        let trm = [unsafeTerm|\c -> let (a,b) = c in let x = a 10 in a True|]
        shouldTyErr (inferTerm' trm)

    describe "fixpoint" $ do
      it "fix f. 10 : Nat" $ do
        inferTerm' [unsafeTerm|fix f. 10|] `shouldSolve`
          (toScheme $ tynat)

      it "fix f. \\x -> 10 : a -> Nat" $ do
        inferTerm' [unsafeTerm|fix f. \x -> 10|] `shouldSolve`
          (Forall ["0a"] $ "0a" |-> tynat)

      it "fix f. \\x y -> 10 : a -> Nat" $ do
        inferTerm' [unsafeTerm|fix f. \x -> 10|] `shouldSolve`
          (Forall ["0a"] $ "0a" |-> tynat)

    describe "out" $ do

      let trm = [unsafeTerm|\x -> let y = out (mu a. Nat * a) x in y|]
      let typ = tyrec "a" (tynat .*. "a")
            |-> tynat .*. tylater (tyrec "a" (tynat .*. "a"))
      it (ppshow trm) $
        inferTerm' trm `shouldSolve`
          (toScheme $ typ)

      let trm = [unsafeTerm|\x -> let (y,z) = out (mu a. Nat * a) x in y|]
      let typ = tyrec "a" (tynat .*. "a")
            |-> tynat
      it (ppshow trm) $
        inferTerm' trm `shouldSolve`
          (toScheme $ typ)

      let trm = [unsafeTerm|\x -> let (y,z) = out (mu a. b * a) x in y|]
      let typ = Forall ["0a"] $   tyrec "a" ("0a" .*. "a")
                          |-> "0a"
      it (ppshow trm) $
        inferTerm' trm `shouldSolve`
          (typ)

    describe "into" $ do
      let trm = [unsafeTerm|\x -> into (mu af. Nat) x|]
      it (ppshow trm) $ do
        inferTerm' trm `shouldSolve`
          (toScheme $ tynat |-> tyrec "af" tynat)

      let trm = [unsafeTerm|into (mu af. Nat) 10|]
      it (ppshow trm) $ do
        inferTerm' trm `shouldSolve`
          (toScheme $ tyrec "af" tynat)

      let trm = [unsafeTerm|\x -> into (mu af. Nat * af) (10, x)|]
      it (ppshow trm) $ do
        inferTerm' trm `shouldSolve`
          (toScheme $  tylater (tyrec "af" (tynat .*. "af"))
                   |-> tyrec "af" (tynat .*. "af"))

      let trm = [unsafeTerm|
        \x -> let (y,z) = out (mu af. Nat * af) x in
              into (mu af. Nat * af) (y, z)
      |]
      it (ppshow trm) $
        inferTerm' trm `shouldSolve`
          (toScheme $
            tyrec "af" (tynat .*. "af") |-> tyrec "af" (tynat .*. "af"))

      let trm = [unsafeTerm|
        fix f. \us ->
          let (u, delay(us')) = out (mu af. tyalloc * af) us
          in into (mu af. tynat * af) (10, delay(u, f us'))
      |]
      it (ppshow trm) $
        inferTerm' trm `shouldSolve`
          (toScheme $ tyrec "af" (tyalloc .*. "af")
                  |-> tyrec "af" (tynat .*. "af"))

      let trm = [unsafeDecl|
        nats : (mu af. alloc * af) -> Nat -> (mu af. Nat * af)
        nats us n =
          let (u, delay(us')) = out (mu af. alloc * af) us in
          let stable(x) = promote(n) in
          into (mu af. Nat * af) (x, delay(u, nats us' (x + 1))).
      |]
      it "nats with rec types" $ do
        inferTerm' (_body trm) `shouldSolve`
          (toScheme $  (tyrec "af" (tyalloc .*. "af"))
                   |-> tynat
                   |-> tyrec "af" (tynat .*. "af"))

      let trm = [unsafeDecl|
        const : (mu af. alloc * af) -> Nat -> (mu af. Nat * af)
        const us n =
          let (u, delay(us')) = out (mu af. alloc * af) us in
          let stable(x) = promote(n) in
          into (mu af. Nat * af) (x, delay(u, const us' x)).
      |]
      it "const with rec types" $ do
        inferTerm' (_body trm) `shouldSolve`
          (toScheme $
                  (tyrec "af" (tyalloc .*. "af"))
              |-> tynat
              |-> tyrec "af" (tynat .*. "af"))

      let trm = [unsafeDecl|
        tails : (mu af. alloc * af) -> (mu af. a * af) -> (mu af. (mu bf. a * bf) * af)
        tails us xs =
          let (u, delay(us')) = out (mu af. alloc * af) us in
          let (x, delay(xs')) = out (mu af. a * af) xs in
          into (mu af. (mu bf. a * bf) * af) (xs, delay(u, ((tails us') xs'))).
      |]
      it "tails with rec types" $ do
        inferTerm' (_body trm) `shouldSolve`
          (Forall ["0a"] $
                  (tyrec "af" (tyalloc .*. "af"))
              |-> tyrec "af" ("0a" .*. "af")
              |-> tyrec "af" ((tyrec "bf" $ "0a" .*. "bf") .*. "af"))

    describe "stable" $ do
      let trm = [unsafeTerm|
                \(fn : #(Nat -> Nat) -> Nat -> Nat) ->
                    let f = stable(\x -> x + 1) in
                    fn f 0
                |]

      it (ppshow trm) $ do
        inferTerm' trm `shouldSolve`
          (toScheme $ (tystable (tynat |-> tynat) |-> tynat |-> tynat) |-> tynat)

      let trm = [unsafeTerm|
                \(fn : #(Nat -> Nat) -> Nat -> Nat) ->
                    let f = \x -> x + 1 in
                    fn f 0
                |]
      it ("fails " ++ ppshow trm) $ do
        shouldTyErr (inferTerm' trm)

      it ("fails " ++ ppshow frp_incr_fails) $ do
        shouldTyErr (inferTerm' $ _body frp_incr_fails)

    describe "type annotations" $ do
      describe "lambdas" $ do
        let trm = [unsafeTerm|\(x:Nat) -> x * 10|]
        it (ppshow trm) $
          inferTerm' trm `shouldSolve`
            (toScheme $ tynat |-> tynat)

        let trm = [unsafeTerm|\(x:a) -> x * 10|]
        it (ppshow trm) $
          inferTerm' trm `shouldSolve`
            (toScheme $ tynat |-> tynat)

        let trm = [unsafeTerm|\(x:Bool) (y:Nat) -> y < 10 && x|]
        it (ppshow trm) $
          inferTerm' trm `shouldSolve`
            (toScheme $ tybool |-> tynat |-> tybool)

        let trm = [unsafeTerm|\(x : @(S Nat)) (y:Nat) -> cons(y, x)|]
        it (ppshow trm) $
          inferTerm' trm `shouldSolve`
            (toScheme $ tylater (tystream tynat) |-> tynat |-> tystream (tynat))

      describe "fixpoints" $ do

        let trm = [unsafeTerm|
          fix (f : S alloc -> S Nat). \us ->
            let cons(u,delay(us')) = us in
            cons(10, delay(u, f us'))
        |]
        it (ppshow trm) $
          inferTerm' trm `shouldSolve`
            (toScheme $ tystream tyalloc |-> tystream tynat)

        let trm = [unsafeTerm|
          fix (f : S alloc -> #a -> S a). \us x ->
            let cons(u,delay(us')) = us in
            let stable(x') = x in
            cons(x', delay(u, f us' stable(x')))
        |]
        it (ppshow trm) $
          inferTerm' trm `shouldSolve`
            (Forall ["0a"] $ tystream tyalloc |-> tystable "0a" |-> tystream "0a")

  describe "test functions" $ do
    it "works for const" $ do
      inferDecl' (frp_const) `shouldSolve`
        (toScheme $ tystream tyalloc |-> tynat |-> tystream tynat)

    it "works for const_fix" $ do
      inferDecl' (frp_const_fix) `shouldSolve`
        (toScheme $ tystream tyalloc |-> tynat |-> tystream tynat)

    it "works for nats" $ do
      inferTerm' (_body frp_nats) `shouldSolve`
        (Forall [] $ tystream tyalloc |-> tynat |-> tystream tynat)

    it "works for map" $ do
      inferTerm' (_body frp_map) `shouldSolve`
        (Forall ["0a","0b"] $ tystream tyalloc
                        |-> tystable ("0a" |-> "0b")
                        |-> tystream "0a"
                        |-> tystream "0b")

    it "works for tails" $ do
      inferTerm' (_body frp_tails) `shouldSolve`
        (Forall ["0a"] $ tystream tyalloc
                        |-> tystream "0a"
                        |-> tystream (tystream "0a"))

    it "works for sum_acc" $ do
      inferTerm' (_body frp_sum_acc) `shouldSolve`
        (toScheme $ tystream tyalloc
                  |-> tystream tynat
                  |-> tynat
                  |-> tystream tynat)

    it "works for unfold" $ do
      inferTerm' (_body frp_unfold) `shouldSolve`
        (Forall ["0a","0b"]
          $   tystream tyalloc
          |-> tystable ("0b" |-> "0a" .*. tylater "0b")
          |-> "0b"
          |-> tystream "0a")

    it "works for swap" $ do
      inferTerm' (_body frp_swap) `shouldSolve`
        (Forall ["0a"]
          $   tystream tyalloc
          |-> tynat
          |-> tystream "0a"
          |-> tystream "0a"
          |-> tystream "0a")

    it "works for switch" $ do
      inferTerm' (_body frp_switch) `shouldSolve`
        (Forall ["0a"]
          $   tystream tyalloc
          |-> tystream "0a"
          |-> (tyrec "b" (tystream "0a" .+. "b"))
          |-> tystream "0a")

    it "works for bind" $ do
      inferTerm' (_body frp_bind) `shouldSolve`
        (Forall ["0a", "0b"]
          $   (tystream tyalloc)
          |-> tystable ("0a" |-> (tyrec "af" ("0b" .+. "af")))
          |-> tyrec "af" ("0a" .+. "af")
          |-> tyrec "af" ("0b" .+. "af"))


  describe "negative cases" $ do
    let trm = [unsafeTerm|\x -> x + 10 < (x && True)|]
    it (ppshow trm) $ do
      shouldTyErr (inferTerm' trm)

    let trm = [unsafeTerm|\x -> x x|]
    it (ppshow trm) $ do
      shouldTyErr (inferTerm' trm)

    let trm = [unsafeTerm|\x -> x + 10 - (x x)|]
    it (ppshow trm) $ do
      shouldTyErr (inferTerm' trm)

    let trm = [unsafeTerm|\x -> let (y,z) = x in x + 10|]
    it (ppshow trm) $ do
      shouldTyErr (inferTerm' trm)

    let trm = [unsafeTerm|\x -> let (y,z) = out (Nat * Nat) x in z + 10|]
    it (ppshow trm) $ do
      shouldTyErr (inferTerm' trm)

    let trm = [unsafeTerm|
      \x -> let (y,z) = out (mu af. Nat * af) x in
            into (mu af. Bool * af) (y, z)
    |]

    let trm = [unsafeTerm|\x -> let cons(y,cons(y',ys)) = x in cons(y,ys)|]
    it (ppshow trm) $ do
      shouldTyErr (inferTerm' trm)

    let trm = [unsafeTerm|\(x:Nat) -> x && False|]
    it (ppshow trm) $ do
      shouldTyErr (inferTerm' trm)

    let trm = [unsafeTerm|\(x:Nat -> Bool) -> x 10 + 10|]
    it (ppshow trm) $ do
      shouldTyErr (inferTerm' trm)

    let trm = [unsafeTerm|\x -> let stable(y) = promote(x) in True|]
    it (ppshow trm) $ do
      shouldTyErr (inferTerm' trm)


    it "scary_const_fails" $ do
      shouldTyErr (inferDecl' frp_scary_const_fails)





