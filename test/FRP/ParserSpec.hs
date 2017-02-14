{-# LANGUAGE QuasiQuotes, OverloadedStrings #-}

module FRP.ParserSpec where

import Test.Hspec
import FRP.AST
import FRP.Parser.Term
import FRP.Parser.Type
import FRP.Parser.Decl
import FRP.Pretty (ppputStrLn)

import Control.Monad.State
import Debug.Trace
import qualified Data.Map.Strict as M
import Data.List (unfoldr)

import Text.ParserCombinators.Parsec (parse)
import NeatInterpolation
import Data.Text (Text, pack, unpack)

frp_const =
  [text|
  \n -> \us ->
    let cons(u, delay(us')) = us in
    let stable(x) = promote(n) in
    cons(x, delay (u, const us' x))
  |]

frp_sum_acc =
  [text|
  \us -> \ns -> \acc ->
    let cons(u, delay(us')) = us in
    let cons(n, delay(ns')) = ns in
    let stable(x) = promote(n + acc) in
    cons(x, delay(u, sum_acc us' ns' x))
  |]

frp_map =
  [text|
  \us -> \h -> \xs ->
    let cons(u, delay(us')) = us in
    let cons(x, delay(xs')) = xs in
    let stable(f)           = h  in
    cons(f x, delay(u, map us' stable(f) xs'))
  |]

frp_swap =
  [text|
  \us -> \n -> \xs -> \ys ->
    if n == 0 then
      ys
    else
      let cons(u, delay(us')) = us in
      let cons(x, delay(xs')) = xs in
      let cons(y, delay(ys')) = ys in
      let stable(m) = promote(n)   in
      cons(x, delay(u, swap us' (m - 1) xs' ys'))
  |]

frp_switch =
  [text|
  \us -> \xs -> \e ->
    let cons(u, delay(us')) = us in
    let cons(x, delay(xs')) = xs in
    case out e of
      | inl ys -> ys
      | inr t  -> let delay(e') = t in
                  cons(x, delay (u, switch us' xs' e')))
  |]

frp_bind =
  [text|
  \us -> \h -> \e ->
    let cons(u, delay(us')) = us in
    let stable(f)           = h  in
    case out e of
      | inl a -> f a
      | inr t -> let delay(e') = t in
                 into (inr (delay (u, bind us' stable(f) e')))
  |]

tmbool = TmLit . LBool

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  describe "term parsing" $ do
    it "should parse lambda expressions" $ do
      parse tmlam "lam" "\\x -> x" `shouldBe` Right (TmLam "x" "x")
      parse term "lam" "\\x  -> x" `shouldBe` Right (TmLam "x" "x")
      parse term "lam" "\\x  -> x + x" `shouldBe`
        Right (TmLam "x" ("x" + "x"))

      parse term "lam" "\\x -> \\y -> x + y" `shouldBe`
        Right (TmLam "x" $ TmLam "y" ("x" + "y"))

    it "should parse let expressions" $ do
      parse tmlet "let" "let x = 10 in x" `shouldBe`
        Right (TmLet "x" 10 "x")
      parse term "let" "let x = 10 in x" `shouldBe`
        Right (TmLet "x" 10 "x")
      parse term "let" "let x = y in\n x * y" `shouldBe`
        Right (TmLet "x" "y" ("x" * "y"))
      parse term "let" "let x = 10 in let y = 42 in x * y" `shouldBe`
        Right (TmLet "x" 10 $ TmLet "y" 42 ("x" * "y"))

      -- should still work if we change the var names
      parse term "let" "let outro = 10 in let y = 42 in outro * y" `shouldBe`
        Right (TmLet "outro" 10 $ TmLet "y" 42 ("outro" * "y"))

      parse term "let" "10 + let x = 10 in let y = 42 in x * y" `shouldBe`
        Right (10 + (TmLet "x" 10 $ TmLet "y" 42 ("x" * "y")))

    it "should parse cons expressions" $ do
      parse tmcons "cons" "cons(10, 20)" `shouldBe`
        Right (TmCons 10 20)
      parse tmcons "cons" "cons ( 10  , 20  )  " `shouldBe`
        Right (TmCons 10 20)
      parse term "term" "cons(10, 20)" `shouldBe`
        Right (TmCons 10 20)
      parse term "term" "cons ( 10  , 20  )  " `shouldBe`
        Right (TmCons 10 20)

    it "should parse tuple projections" $ do
      parse term "fst" "\\y -> let x = fst y in x * 10" `shouldBe`
        Right (TmLam "y" $ TmLet "x" (TmFst "y") $ "x" * 10)
      parse term "snd" "\\y -> let x = snd y in x * 10" `shouldBe`
        Right (TmLam "y" $ TmLet "x" (TmSnd "y") $ "x" * 10)

      parse term "snd and fst" "\\z -> let x = fst z in let y = snd z in x * y" `shouldBe`
        Right (TmLam "z" $ TmLet "x" (TmFst "z") $ TmLet "y" (TmSnd "z") $ "x" * "y")

    it "parses application" $ do
      parse term "app" "x x" `shouldBe`
        Right (TmApp "x" "x")

      parse term "app" "\\x -> let y = 10 in x (y * 2)" `shouldBe`
        Right (TmLam "x" $ TmLet "y" 10 $ TmApp "x" ("y" * 2))

      parse term "app" "\\f -> let x = f x in x" `shouldBe`
        Right (TmLam "f" $ TmLet "x" (TmApp "f" "x") "x")

      parse term "app" "10 + (\\x -> x * 2) 4" `shouldBe`
        Right (10 + TmApp (TmLam "x" $ "x" * 2) 4)

    it "parses nested patterns" $ do
      parse term "pats" "let cons(u, delay(us')) = us in u" `shouldBe`
        Right (TmLet (PCons "u" (PDelay "us'")) "us" "u")

    it "parses if-then-else" $ do
      parse tmite "ite" "if x == 10 then True else False" `shouldBe`
        Right (TmITE (TmBinOp Eq "x" 10) (tmbool True) (tmbool False))

      parse term "ite" "if x == 10 then True else False" `shouldBe`
        Right (TmITE (TmBinOp Eq "x" 10) (tmbool True) (tmbool False))

      parse term "ite" "if x > 10 then x + 10 else x == 20" `shouldBe`
        Right (TmITE (TmBinOp Gt "x" 10)
                     ("x" + 10)
                     (TmBinOp Eq "x" 20)
              )

      parse term "ite" "42 + if x > 10 then x + 10 else x == 20" `shouldBe`
        Right (42 + TmITE (TmBinOp Gt "x" 10)
                     ("x" + 10)
                     (TmBinOp Eq "x" 20)
              )

    it "parses case exprs" $ do
      parse tmcase "case 1" "case x of | inl y -> 10 | inr z -> 20" `shouldBe`
        Right (TmCase "x" ("y", 10) ("z", 20))

      parse term "case 2" "10 + case x of | inl y -> 10 | inr z -> 4 + 1" `shouldBe`
        Right (10 + TmCase "x" ("y", 10) ("z", 4 + 1))

      let nested_case =
            [text|
            case x of
              | inl y -> case y of
                | inl yy -> yy * 10
                | inr yz -> yz - 10
              | inr z -> case z of
                | inl zy -> zy * 10
                | inr zz -> zz + 10
            |]
      parse term "nested case" (unpack nested_case) `shouldBe`
        Right (TmCase "x"
                ("y", TmCase "y" ("yy", "yy" * 10) ("yz", "yz" - 10))
                ("z", TmCase "z" ("zy", "zy" * 10) ("zz", "zz" + 10))
              )

    it "parses compound expressions" $ do
      parse term "frp" "\\x -> \\y -> let z = x + y in cons(x, z * x + y)" `shouldBe`
        Right (TmLam "x" $ TmLam "y" $ TmLet "z" ("x" + "y") $ TmCons "x" ("z" * "x" + "y"))

      parse term "frp" "let y = 2 * 10 in (\\x -> 2 * x) (y + 2)" `shouldBe`
        Right (TmLet "y" (2 * 10) $ TmApp (TmLam "x" (2 * "x")) ("y" + 2))

      let frp_const_ast =
            TmLam "n" $ TmLam "us" $
              TmLet (PCons "u" (PDelay "us'")) "us" $
              TmLet (PStable "x") (TmPromote "n") $
              TmCons "x" (TmDelay "u" $ "const" `TmApp` "us'" `TmApp` "x")

      parse term "frp_const" (unpack frp_const) `shouldBe` Right (frp_const_ast)

      let frp_sum_acc_ast =
            TmLam "us" $ TmLam "ns" $ TmLam "acc" $
              TmLet (PCons "u" (PDelay "us'")) "us" $
              TmLet (PCons "n" (PDelay "ns'")) "ns" $
              TmLet (PStable "x") (TmPromote ("n" + "acc")) $
              TmCons "x" (TmDelay "u" $ "sum_acc" `TmApp` "us'" `TmApp` "ns'" `TmApp` "x")

      parse term "frp_sum_acc" (unpack frp_sum_acc) `shouldBe` Right (frp_sum_acc_ast)

      let frp_map_ast =
            TmLam "us" $ TmLam "h" $ TmLam "xs" $
              TmLet (PCons "u" (PDelay "us'")) "us" $
              TmLet (PCons "x" (PDelay "xs'")) "xs" $
              TmLet (PStable "f") "h" $
              TmCons ("f" `TmApp` "x")
                     (TmDelay "u" $ "map" `TmApp` "us'" `TmApp` TmStable "f" `TmApp` "xs'")

      parse term "frp_map" (unpack frp_map) `shouldBe` Right (frp_map_ast)

      let frp_swap_ast =
            TmLam "us" $ TmLam "n" $ TmLam "xs" $ TmLam "ys" $
              TmITE (TmBinOp Eq "n" 0) "ys" $
                TmLet (PCons "u" (PDelay "us'")) "us" $
                TmLet (PCons "x" (PDelay "xs'")) "xs" $
                TmLet (PCons "y" (PDelay "ys'")) "ys" $
                TmLet (PStable "m") (TmPromote "n") $
                TmCons "x"
                       (TmDelay "u" $ "swap" `TmApp` "us'" `TmApp`
                                      ("m" - 1) `TmApp` "xs'" `TmApp` "ys'"
                       )

      parse term "frp_swap" (unpack frp_swap) `shouldBe` Right (frp_swap_ast)

      let frp_switch_ast =
            TmLam "us" $ TmLam "xs" $ TmLam "e" $
              TmLet (PCons "u" (PDelay "us'")) "us" $
              TmLet (PCons "x" (PDelay "xs'")) "xs" $
              TmCase (TmOut "e")
                ("ys", "ys")
                ("t", TmLet (PDelay "e'") "t" $
                 TmCons "x"
                        (TmDelay "u" $
                           "switch" `TmApp` "us'" `TmApp` "xs'" `TmApp` "e'"
                        )
                )

      parse term "frp_switch" (unpack frp_switch) `shouldBe` Right (frp_switch_ast)

      let frp_bind_ast =
            TmLam "us" $ TmLam "h" $ TmLam "e" $
              TmLet (PCons "u" (PDelay "us'")) "us" $
              TmLet (PStable "f") "h" $
              TmCase (TmOut "e")
                ("a", "f" `TmApp` "a")
                ("t", TmLet (PDelay "e'") "t" $
                      TmInto (TmInr $ TmDelay "u" $
                             "bind" `TmApp` "us'" `TmApp` TmStable "f" `TmApp` "e'"
                             )
                )

      parse term "frp_bind" (unpack frp_bind) `shouldBe` Right (frp_bind_ast)

  describe "type parsing" $ do
    it "parses Nat" $ do
      parse ty "nat" "Nat" `shouldBe` Right TyNat
    it "parses alloc" $ do
      parse ty "alloc" "alloc" `shouldBe` Right TyAlloc
    it "parses streams" $ do
      parse ty "stream of nats" "S Nat" `shouldBe`
        Right (TyStream TyNat)
      parse ty "stream of allocs" "S alloc" `shouldBe`
        Right (TyStream TyAlloc)
      parse ty "stream of params" "S a" `shouldBe`
        Right (TyStream $ TyParam "a")
      parse ty "stream of params" "S s" `shouldBe`
        Right (TyStream $ TyParam "s")
      parse ty "stream of params" "S Sample" `shouldBe`
        Right (TyStream $ TyParam "Sample")
    it "parses products" $ do
      parse ty "pair of nats" "Nat * Nat" `shouldBe`
        Right (TyProd TyNat TyNat)
      parse ty "pair of nat x alloc" "Nat * alloc" `shouldBe`
        Right (TyProd TyNat TyAlloc)
      parse ty "pair of params" "a * b" `shouldBe`
        Right (TyProd (TyParam "a") (TyParam "b"))
      parse ty "pair of streams of nats" "S Nat * S Nat" `shouldBe`
        Right (TyProd (TyStream TyNat) (TyStream TyNat))
      parse ty "nested pair" "Nat * Nat * Nat" `shouldBe`
        Right (TyProd TyNat (TyProd TyNat TyNat))
    it "parses sums" $ do
      parse ty "sum of nats" "Nat + Nat" `shouldBe`
        Right (TySum TyNat TyNat)
      parse ty "sum of nat x alloc" "Nat + alloc" `shouldBe`
        Right (TySum TyNat TyAlloc)
      parse ty "sum of params" "a + b" `shouldBe`
        Right (TySum (TyParam "a") (TyParam "b"))
      parse ty "sum of streams of nats" "S Nat + S Nat" `shouldBe`
        Right (TySum (TyStream TyNat) (TyStream TyNat))
      parse ty "nested sum" "Nat + Nat + Nat" `shouldBe`
        Right (TySum TyNat (TySum TyNat TyNat))
    it "parses arrows" $ do
      parse ty "arrow of nats" "Nat -> Nat" `shouldBe`
        Right (TyArr TyNat TyNat)
      parse ty "arrow of nat x alloc" "Nat -> alloc" `shouldBe`
        Right (TyArr TyNat TyAlloc)
      parse ty "arrow of params" "a -> b" `shouldBe`
        Right (TyArr (TyParam "a") (TyParam "b"))
      parse ty "arrow of streams of nats" "S Nat -> S Nat" `shouldBe`
        Right (TyArr (TyStream TyNat) (TyStream TyNat))
      parse ty "nested arrows" "Nat -> Nat -> Nat" `shouldBe`
        Right (TyArr TyNat (TyArr TyNat TyNat))
    it "parses later" $ do
      parse ty "later Nat" "@Nat" `shouldBe`
        Right (TyLater TyNat)
      parse ty "later Alloc" "@alloc" `shouldBe`
        Right (TyLater TyAlloc)
      parse ty "later S Alloc" "@(S alloc)" `shouldBe`
        Right (TyLater $ TyStream TyAlloc)
      parse ty "later Nat -> Nat" "@(Nat -> Nat)" `shouldBe`
        Right (TyLater $ TyArr TyNat TyNat)
      parse ty "later Nat * Nat" "@(Nat * Nat)" `shouldBe`
        Right (TyLater $ TyProd TyNat TyNat)
    it "parses stable" $ do
      parse ty "stable Nat" "#Nat" `shouldBe`
        Right (TyStable TyNat)
      parse ty "stable Alloc" "#alloc" `shouldBe`
        Right (TyStable TyAlloc)
      parse ty "stable S Alloc" "#(S alloc)" `shouldBe`
        Right (TyStable $ TyStream TyAlloc)
      parse ty "stable Nat -> Nat" "#(Nat -> Nat)" `shouldBe`
        Right (TyStable $ TyArr TyNat TyNat)
      parse ty "stable Nat * Nat" "#(Nat * Nat)" `shouldBe`
        Right (TyStable $ TyProd TyNat TyNat)
    it "parses compund types" $ do
      parse ty "c1" "S Nat -> #(S A) -> X" `shouldBe`
        Right (TyStream TyNat `TyArr` TyStable (TyStream "A") `TyArr` "X")
      parse ty "map" "S alloc -> #(A -> B) -> S A -> S B" `shouldBe`
        Right (TyStream TyAlloc `TyArr` TyStable ("A" `TyArr` "B") `TyArr`
               TyStream "A" `TyArr` TyStream "B")
      parse ty "tails" "S alloc -> S A -> S (S A)" `shouldBe`
        Right (TyStream TyAlloc `TyArr` TyStream "A" `TyArr` TyStream (TyStream "A"))
      parse ty "unfold" "S alloc -> #(X -> A * @X) -> X -> S A" `shouldBe`
        Right (TyStream TyAlloc `TyArr`
               TyStable ("X" `TyArr` TyProd "A" (TyLater "X")) `TyArr`
               "X" `TyArr`
               TyStream "A"
              )
  describe "parsing declarations" $ do
    it "should parse simple decls" $ do
      let tc1 = [text|
                 foo : Nat
                 foo = 5
                |]
      parse decl "decl1" (unpack tc1) `shouldBe`
        Right (Decl (TyNat) "foo" 5)

      let tc2 = [text|
                 foo : Nat
                 foo = 5
                |]
      parse decl "decl1" (unpack tc2) `shouldBe`
        Right (Decl (TyNat) "foo" 5)

