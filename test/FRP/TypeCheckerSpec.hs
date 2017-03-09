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
import           FRP.TestFunctions
import           Data.List            (intercalate)
import           FRP.Parser.Decl
import           Text.Parsec

frp_natfn_text = [text|
  natfn : (S alloc * Nat) -> (Nat * @(S alloc * Nat))
  natfn x =
    let (us, n) = x in
    let cons(u, delay(us')) = us in
    let stable(n') = promote(n) in
    (n, delay(u, (us', n' + 1))).
|]

frp_nat_fn_parse :: Either ParseError (Decl (SourcePos))
frp_nat_fn_parse = parse decl "" (unpack frp_natfn_text)

frp_natfn = case frp_nat_fn_parse of
  Right decl -> decl
  Left e     -> error (show e)

frp_nats_unfold_text = [text|
  nats : S alloc -> S Nat
  nats us =
    let fn = stable(natfn) in
    unfold us fn (us, 0).
|]

frp_nats_unfold = case (parse decl "" (unpack frp_nats_unfold_text)) of
  Right decl -> decl
  Left e     -> error (show e)

shouldTC :: (Eq (f ()), Show (f ()), Functor f, Show t)
            => Either (TypeErr t) (f a, Qualifier) -> (f (), Qualifier) -> Expectation
shouldTC eith expect = case eith of
  Left err  -> expectationFailure (ppshow err)
  Right (t,q) -> (unitFunc t, q) `shouldBe` expect

shouldTyErr :: Show t => Either (TypeErr t) (Type t, Qualifier) -> Expectation
shouldTyErr = \case
  Left err -> return ()
  Right (t,q) -> expectationFailure $ show (t, q)

oneline :: String -> String
oneline s = intercalate " " (lines s)

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
      it "works for let y = x in y" $ do
        let ctx = (Ctx (M.singleton "x" (tynat, QNow)))
        runCheckTerm ctx (tmlet "y" "x" "y") `shouldTC` (tynat, QNow)
      it "works for let (x,y) = z in x where z : Nat * Bool" $ do
        let ctx = (Ctx (M.singleton "z" (typrod tynat tybool, QNow)))
        runCheckTerm ctx (tmlet (PTup "x" "y") "z" "x") `shouldTC` (tynat, QNow)
      it "works for let (x,y) = z in y where z : Nat * Bool" $ do
        let ctx = (Ctx (M.singleton "z" (typrod tynat tybool, QNow)))
        runCheckTerm ctx (tmlet (PTup "x" "y") "z" "y") `shouldTC` (tybool, QNow)
      it "works for let stable(y) = promote(x) in delay(u,y)" $ do
        let ctx = Ctx $ M.fromList [("x", (tynat, QNow)), ("u", (tyalloc, QNow))]
        runCheckTerm ctx (tmlet (PStable "y") (tmpromote "x") (tmdelay "u" "y")) `shouldTC` (tylater tynat, QNow)
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
        runCheckTerm' (tmlamty "xs" ((tylater $ tystream tynat)) $
                       tmlamty "x" tynat $ tmcons "x" "xs")
          `shouldTC` ((tylater $ tystream tynat) |-> tynat |-> tystream tynat, QNow)
    describe "cons" $ do
      it "works for cons(x,xs) where x:Nat, xs:@(S Nat)" $ do
        let ctx = Ctx $ M.fromList
              [ ("x", (tynat, QNow))
              , ("xs", (tylater (tystream tynat), QNow))
              ]
        runCheckTerm ctx (tmcons "x" "xs") `shouldTC`
          (tystream tynat, QNow)
    describe "application" $ do
      it "works for \\(f:Nat -> Bool) (x:Nat) -> f x" $ do
        runCheckTerm' (tmlamty "f" (tynat |-> tybool) $
                       tmlamty "x" tynat $ "f" <| "x")
          `shouldTC` ((tynat |-> tybool) |-> tynat |-> tybool, QNow)
      it "works for f 10 where (f : Nat -> Bool)" $ do
        let ctx = Ctx $ M.singleton "f" (tynat |-> tybool, QNow)
        runCheckTerm ctx ("f" <| 10) `shouldTC` (tybool, QNow)
      it "works for f 10 True where (f : Nat -> Bool -> Nat)" $ do
        let ctx = Ctx $ M.singleton "f" (tynat |-> tybool |-> tynat, QNow)
        runCheckTerm ctx ("f" <| 10 <| tmbool True) `shouldTC`
          (tynat, QNow)
    describe "compound expressions" $ do
      let expr = tmlet "x" (tmlamty "y" tynat $ "y" * 20) (("x" <| 1) + 20)
      it ("works for " ++ oneline (ppshow expr)) $ do
        runCheckTerm' expr `shouldTC` (tynat, QNow)

    describe "declarations" $ do
      it "works for frp_nats" $ do
        runCheckDecl' frp_nats `shouldTC` (_type frp_nats, QNow)
          -- (tystream tyalloc |-> tynat |-> tystream tynat, QNow)
      it "works for frp_sum_acc" $ do
        let ty = runCheckDecl' frp_sum_acc
        ty `shouldTC` (_type frp_sum_acc, QNow)
      it "works for frp_sum" $ do
        let ctx = Ctx $ M.singleton "sum_acc" (_type frp_sum_acc, QStable)
        let ty = runCheckDecl ctx frp_sum
        ty `shouldTC` (_type frp_sum, QNow)
      it "works for frp_tails" $ do
        let ty = runCheckDecl' frp_tails
        ty `shouldTC` (_type frp_tails, QNow)
      it "works for frp_map" $ do
        let ty = runCheckDecl' frp_map
        ty `shouldTC` (_type frp_map, QNow)
      it "works for frp_unfold" $ do
        let ty = runCheckDecl' frp_unfold
        ty `shouldTC` (_type frp_unfold, QNow)
      it "works for frp_swap" $ do
        let ty = runCheckDecl' frp_swap
        ty `shouldTC` (_type frp_swap, QNow)
      it "works for frp_natfn" $ do
        let natfn = unitFunc frp_natfn
        let ty = runCheckDecl' natfn
        ty `shouldTC` (_type natfn, QNow)
      it "works for frp_nats_unfold" $ do
        let fn = unitFunc frp_nats_unfold
        let ctx = Ctx $ M.fromList
                    [ ("unfold", (_type frp_unfold, QStable))
                    , ("natfn", (_type $ unitFunc frp_natfn, QStable))
                    ]
        let ty = runCheckDecl ctx fn
        ty `shouldTC` (_type fn, QNow)

      -- it "works for frp_fib" $ do
      --   ppputStrLn frp_fib
      --   let ctx = Ctx $ M.singleton "unfold" (_type frp_unfold, QStable)
      --   let ty = runCheckDecl ctx frp_fib
      --   ty `shouldTC` (_type frp_fib, QNow)

