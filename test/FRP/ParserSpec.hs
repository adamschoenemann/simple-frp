{-# LANGUAGE QuasiQuotes, OverloadedStrings #-}

module FRP.ParserSpec where

import Test.Hspec
import FRP.AST
import FRP.AST.Construct
import qualified FRP.Parser.Term as P
import qualified FRP.Parser.Type as P
import qualified FRP.Parser.Decl as P
import qualified FRP.Parser.Program as P
import FRP.Pretty (ppputStrLn, ppshow)

import Control.Monad.State
import Debug.Trace
import qualified Data.Map.Strict as M
import Data.List (unfoldr)

import Text.ParserCombinators.Parsec (parse)
import NeatInterpolation
import Data.Text (Text, pack, unpack)

import Data.Either (isRight)
import FRP.TestFunctions (frps)


frp_nats =
  [text|
  \n us ->
    let cons(u, delay(us')) = us in
    let stable(x) = promote(n) in
    cons(x, delay (u, const us' (x + 1)))
  |]

frp_const =
  [text|
  \n us ->
    let cons(u, delay(us')) = us in
    let stable(x) = promote(n) in
    cons(x, delay (u, const us' x))
  |]

frp_sum_acc =
  [text|
  \us ns acc ->
    let cons(u, delay(us')) = us in
    let cons(n, delay(ns')) = ns in
    let stable(x) = promote(n + acc) in
    cons(x, delay(u, sum_acc us' ns' x))
  |]

frp_map =
  [text|
  \us h xs ->
    let cons(u, delay(us')) = us in
    let cons(x, delay(xs')) = xs in
    let stable(f)           = h  in
    cons(f x, delay(u, map us' stable(f) xs'))
  |]

frp_swap =
  [text|
  \us n xs ys ->
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
  \us xs e ->
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

tmbool = tmlit . LBool

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  describe "term parsing" $ do
    it "should parse lambda expressions" $ do
      parse P.tmlam "lam" "\\x -> x" `shouldBe` Right ("x" --> "x")
      parse P.term "lam" "\\x  -> x" `shouldBe` Right ("x" --> "x")
      parse P.term "lam" "\\x  -> x + x" `shouldBe`
        Right ("x" --> ("x" + "x"))

      parse P.term "lam" "\\x -> \\y -> x + y" `shouldBe`
        Right ("x" --> "y" --> ("x" + "y"))

      parse P.term "lam1" "\\x y z -> y" `shouldBe`
        Right ("x" --> "y" --> "z" --> "y")

    it "should parse let expressions" $ do
      parse P.tmlet "let" "let x = 10 in x" `shouldBe`
        Right (tmlet "x" 10 "x")
      parse P.term "let" "let x = 10 in x" `shouldBe`
        Right (tmlet "x" 10 "x")
      parse P.term "let" "let x = y in\n x * y" `shouldBe`
        Right (tmlet "x" "y" ("x" * "y"))
      parse P.term "let" "let x = 10 in let y = 42 in x * y" `shouldBe`
        Right (tmlet "x" 10 $ tmlet "y" 42 ("x" * "y"))

      -- should still work if we change the var names
      parse P.term "let" "let outro = 10 in let y = 42 in outro * y" `shouldBe`
        Right (tmlet "outro" 10 $ tmlet "y" 42 ("outro" * "y"))

      parse P.term "let" "10 + let x = 10 in let y = 42 in x * y" `shouldBe`
        Right (10 + (tmlet "x" 10 $ tmlet "y" 42 ("x" * "y")))

    it "should parse cons expressions" $ do
      parse P.tmcons "cons" "cons(10, 20)" `shouldBe`
        Right (tmcons 10 20)
      parse P.tmcons "cons" "cons ( 10  , 20  )  " `shouldBe`
        Right (tmcons 10 20)
      parse P.term "term" "cons(10, 20)" `shouldBe`
        Right (tmcons 10 20)
      parse P.term "term" "cons ( 10  , 20  )  " `shouldBe`
        Right (tmcons 10 20)

    it "should parse tuples" $ do
      parse P.term "tup1" "(x,y)" `shouldBe` Right (tmtup "x" "y")
      parse P.term "tup2" "(x,(y, x+y))" `shouldBe` Right (tmtup "x" (tmtup "y" ("x" + "y")))
      parse P.term "tup3" "fst (x,y) * 20" `shouldBe`
        Right ((tmfst (tmtup "x" "y")) * 20)

    it "should parse tuple projections" $ do
      parse P.term "fst" "\\y -> let x = fst y in x * 10" `shouldBe`
        Right ("y" --> tmlet "x" (tmfst "y") $ "x" * 10)
      parse P.term "snd" "\\y -> let x = snd y in x * 10" `shouldBe`
        Right ("y" --> tmlet "x" (tmsnd "y") $ "x" * 10)

      parse P.term "snd and fst" "\\z -> let x = fst z in let y = snd z in x * y" `shouldBe`
        Right ("z" --> tmlet "x" (tmfst "z") $ tmlet "y" (tmsnd "z") $ "x" * "y")

    it "parses application" $ do
      parse P.term "app" "x x" `shouldBe`
        Right ("x" <| "x")

      parse P.term "app" "\\x -> let y = 10 in x (y * 2)" `shouldBe`
        Right ("x" --> tmlet "y" 10 $ "x" <| ("y" * 2))

      parse P.term "app" "\\f -> let x = f x in x" `shouldBe`
        Right ("f" --> tmlet "x" ("f" <| "x") "x")

      parse P.term "app" "10 + (\\x -> x * 2) 4" `shouldBe`
        Right (10 + ("x" --> "x" * 2) <| 4)

    it "parses nested patterns" $ do
      parse P.term "pats" "let cons(u, delay(us')) = us in u" `shouldBe`
        Right (tmlet (PCons "u" (PDelay "us'")) "us" "u")

    it "parses if-then-else" $ do
      parse P.tmite "ite" "if x == 10 then True else False" `shouldBe`
        Right (tmite ("x" === 10) (tmbool True) (tmbool False))

      parse P.term "ite" "if x == 10 then True else False" `shouldBe`
        Right (tmite ("x" === 10) (tmbool True) (tmbool False))

      parse P.term "ite" "if x > 10 then x + 10 else x == 20" `shouldBe`
        Right (tmite ("x" >. 10)
                     ("x" + 10)
                     ("x" === 20)
              )

      parse P.term "ite" "42 + if x > 10 then x + 10 else x == 20" `shouldBe`
        Right (42 + tmite ("x" >. 10)
                     ("x" + 10)
                     ("x" === 20)
              )

    it "parses case exprs" $ do
      parse P.tmcase "case 1" "case x of | inl y -> 10 | inr z -> 20" `shouldBe`
        Right (tmcase "x" ("y", 10) ("z", 20))

      parse P.term "case 2" "10 + case x of | inl y -> 10 | inr z -> 4 + 1" `shouldBe`
        Right (10 + tmcase "x" ("y", 10) ("z", 4 + 1))

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
      parse P.term "nested case" (unpack nested_case) `shouldBe`
        Right (tmcase "x"
                ("y", tmcase "y" ("yy", "yy" * 10) ("yz", "yz" - 10))
                ("z", tmcase "z" ("zy", "zy" * 10) ("zz", "zz" + 10))
              )

    it "parses compound expressions" $ do
      parse P.term "frp" "\\x -> \\y -> let z = x + y in cons(x, z * x + y)" `shouldBe`
        Right ("x" --> "y" --> tmlet "z" ("x" + "y") $ tmcons "x" ("z" * "x" + "y"))

      parse P.term "frp" "let y = 2 * 10 in (\\x -> 2 * x) (y + 2)" `shouldBe`
        Right (tmlet "y" (2 * 10) $ ("x" --> 2 * "x") <| ("y" + 2))

      let frp_const_ast =
            "n" --> "us" -->
              tmlet (PCons "u" (PDelay "us'")) "us" $
              tmlet (PStable "x") (tmpromote "n") $
              tmcons "x" (tmdelay "u" $ "const" <| "us'" <| "x")

      parse P.term "frp_const" (unpack frp_const) `shouldBe` Right (frp_const_ast)

      let frp_sum_acc_ast =
            "us" --> "ns" --> "acc" -->
              tmlet (PCons "u" (PDelay "us'")) "us" $
              tmlet (PCons "n" (PDelay "ns'")) "ns" $
              tmlet (PStable "x") (tmpromote ("n" + "acc")) $
              tmcons "x" (tmdelay "u" ("sum_acc" <| "us'" <| "ns'" <| "x"))

      parse P.term "frp_sum_acc" (unpack frp_sum_acc) `shouldBe` Right (frp_sum_acc_ast)

      let frp_map_ast =
            "us" --> "h" --> "xs" -->
              tmlet (PCons "u" (PDelay "us'")) "us" $
              tmlet (PCons "x" (PDelay "xs'")) "xs" $
              tmlet (PStable "f") "h" $
              tmcons ("f" <| "x")
                     (tmdelay "u" ("map" <| "us'" <| tmstable "f" <| "xs'"))

      parse P.term "frp_map" (unpack frp_map) `shouldBe` Right (frp_map_ast)

      let frp_swap_ast =
            "us" --> "n" --> "xs" --> "ys" -->
              tmite ("n" === 0) "ys" $
                tmlet (PCons "u" (PDelay "us'")) "us" $
                tmlet (PCons "x" (PDelay "xs'")) "xs" $
                tmlet (PCons "y" (PDelay "ys'")) "ys" $
                tmlet (PStable "m") (tmpromote "n") $
                tmcons "x"
                       (tmdelay "u" $ "swap" <| "us'" <|
                                      ("m" - 1) <| "xs'" <| "ys'"
                       )

      parse P.term "frp_swap" (unpack frp_swap) `shouldBe` Right (frp_swap_ast)

      let frp_switch_ast =
            "us" --> "xs" --> "e" -->
              tmlet (PCons "u" (PDelay "us'")) "us" $
              tmlet (PCons "x" (PDelay "xs'")) "xs" $
              tmcase (tmout "e")
                ("ys", "ys")
                ("t", tmlet (PDelay "e'") "t" $
                 tmcons "x"
                        (tmdelay "u" $
                           "switch" <| "us'" <| "xs'" <| "e'"
                        )
                )

      parse P.term "frp_switch" (unpack frp_switch) `shouldBe` Right (frp_switch_ast)

      let frp_bind_ast =
            "us" --> "h" --> "e" -->
              tmlet (PCons "u" (PDelay "us'")) "us" $
              tmlet (PStable "f") "h" $
              tmcase (tmout "e")
                ("a", "f" <| "a")
                ("t", tmlet (PDelay "e'") "t" $
                      tminto (tminr $ tmdelay "u" $
                             "bind" <| "us'" <| tmstable "f" <| "e'"
                             )
                )

      parse P.term "frp_bind" (unpack frp_bind) `shouldBe` Right (frp_bind_ast)

  describe "type parsing" $ do
    it "parses Nat" $ do
      parse P.ty "nat" "Nat" `shouldBe` Right TyNat
    it "parses alloc" $ do
      parse P.ty "alloc" "alloc" `shouldBe` Right TyAlloc
    it "parses streams" $ do
      parse P.ty "stream of nats" "S Nat" `shouldBe`
        Right (TyStream TyNat)
      parse P.ty "stream of allocs" "S alloc" `shouldBe`
        Right (TyStream TyAlloc)
      parse P.ty "stream of params" "S a" `shouldBe`
        Right (TyStream $ TyParam "a")
      parse P.ty "stream of params" "S s" `shouldBe`
        Right (TyStream $ TyParam "s")
      parse P.ty "stream of params" "S Sample" `shouldBe`
        Right (TyStream $ TyParam "Sample")
    it "parses products" $ do
      parse P.ty "pair of nats" "Nat * Nat" `shouldBe`
        Right (TyProd TyNat TyNat)
      parse P.ty "pair of nat x alloc" "Nat * alloc" `shouldBe`
        Right (TyProd TyNat TyAlloc)
      parse P.ty "pair of params" "a * b" `shouldBe`
        Right (TyProd (TyParam "a") (TyParam "b"))
      parse P.ty "pair of streams of nats" "S Nat * S Nat" `shouldBe`
        Right (TyProd (TyStream TyNat) (TyStream TyNat))
      parse P.ty "nested pair" "Nat * Nat * Nat" `shouldBe`
        Right (TyProd TyNat (TyProd TyNat TyNat))
    it "parses sums" $ do
      parse P.ty "sum of nats" "Nat + Nat" `shouldBe`
        Right (TySum TyNat TyNat)
      parse P.ty "sum of nat x alloc" "Nat + alloc" `shouldBe`
        Right (TySum TyNat TyAlloc)
      parse P.ty "sum of params" "a + b" `shouldBe`
        Right (TySum (TyParam "a") (TyParam "b"))
      parse P.ty "sum of streams of nats" "S Nat + S Nat" `shouldBe`
        Right (TySum (TyStream TyNat) (TyStream TyNat))
      parse P.ty "nested sum" "Nat + Nat + Nat" `shouldBe`
        Right (TySum TyNat (TySum TyNat TyNat))
    it "parses arrows" $ do
      parse P.ty "arrow of nats" "Nat -> Nat" `shouldBe`
        Right (TyArr TyNat TyNat)
      parse P.ty "arrow of nat x alloc" "Nat -> alloc" `shouldBe`
        Right (TyArr TyNat TyAlloc)
      parse P.ty "arrow of params" "a -> b" `shouldBe`
        Right (TyArr (TyParam "a") (TyParam "b"))
      parse P.ty "arrow of streams of nats" "S Nat -> S Nat" `shouldBe`
        Right (TyArr (TyStream TyNat) (TyStream TyNat))
      parse P.ty "nested arrows" "Nat -> Nat -> Nat" `shouldBe`
        Right (TyArr TyNat (TyArr TyNat TyNat))
    it "parses later" $ do
      parse P.ty "later Nat" "@Nat" `shouldBe`
        Right (TyLater TyNat)
      parse P.ty "later Alloc" "@alloc" `shouldBe`
        Right (TyLater TyAlloc)
      parse P.ty "later S Alloc" "@(S alloc)" `shouldBe`
        Right (TyLater $ TyStream TyAlloc)
      parse P.ty "later Nat -> Nat" "@(Nat -> Nat)" `shouldBe`
        Right (TyLater $ TyArr TyNat TyNat)
      parse P.ty "later Nat * Nat" "@(Nat * Nat)" `shouldBe`
        Right (TyLater $ TyProd TyNat TyNat)
    it "parses stable" $ do
      parse P.ty "stable Nat" "#Nat" `shouldBe`
        Right (TyStable TyNat)
      parse P.ty "stable Alloc" "#alloc" `shouldBe`
        Right (TyStable TyAlloc)
      parse P.ty "stable S Alloc" "#(S alloc)" `shouldBe`
        Right (TyStable $ TyStream TyAlloc)
      parse P.ty "stable Nat -> Nat" "#(Nat -> Nat)" `shouldBe`
        Right (TyStable $ TyArr TyNat TyNat)
      parse P.ty "stable Nat * Nat" "#(Nat * Nat)" `shouldBe`
        Right (TyStable $ TyProd TyNat TyNat)
    it "parses compund types" $ do
      parse P.ty "c1" "S Nat -> #(S A) -> X" `shouldBe`
        Right (TyStream TyNat `TyArr` TyStable (TyStream "A") `TyArr` "X")
      parse P.ty "map" "S alloc -> #(A -> B) -> S A -> S B" `shouldBe`
        Right (TyStream TyAlloc `TyArr` TyStable ("A" `TyArr` "B") `TyArr`
               TyStream "A" `TyArr` TyStream "B")
      parse P.ty "tails" "S alloc -> S A -> S (S A)" `shouldBe`
        Right (TyStream TyAlloc `TyArr` TyStream "A" `TyArr` TyStream (TyStream "A"))
      parse P.ty "unfold" "S alloc -> #(X -> A * @X) -> X -> S A" `shouldBe`
        Right (TyStream TyAlloc `TyArr`
               TyStable ("X" `TyArr` TyProd "A" (TyLater "X")) `TyArr`
               "X" `TyArr`
               TyStream "A"
              )
  describe "parsing declarations" $ do
    it "should parse simple decls1" $ do
      let tc1 = [text|
                 foo : Nat
                 foo = 5.
                |]
      parse P.decl "decl1" (unpack tc1) `shouldBe`
        Right (Decl (TyNat) "foo" 5)

    it "should parse simple decls2" $ do
      let tc2 = [text|
                 foo : Nat -> Nat
                 foo = \x -> x.
                |]
      parse P.decl "decl2" (unpack tc2) `shouldBe`
        Right (Decl (TyNat `TyArr` TyNat) "foo" (tmlam "x" "x"))

    it "should parse simple decls3" $ do
      let tc3 = [text|
                 foo : Nat -> S a -> a

                    foo = \a -> \xs ->
                            let cons(x, xs') = xs in
                            x - 1.
                |]
      parse P.decl "decl3" (unpack tc3) `shouldBe`
        Right (Decl (TyNat `TyArr` TyStream "a" `TyArr` "a") "foo"
              ("a" --> "xs" --> tmlet (PCons "x" "xs'") "xs" $ "x" - 1))

    it "should parse simple decls4" $ do
      let tc4 = [text|
                 foo : Nat -> S foo -> foo

                    foo = \a -> \xs ->
                            let cons(x, xs') = xs in
                            x - 1.
                |]
      parse P.decl "decl4" (unpack tc4) `shouldBe`
        Right (Decl (TyNat `TyArr` TyStream "foo" `TyArr` "foo") "foo"
              ("a" --> "xs" --> tmlet (PCons "x" "xs'") "xs" $ "x" - 1))

    it "should parse with param list" $ do
      let tc4 = [text|
                 foo : Nat -> S foo -> foo
                 foo a xs =
                    let cons(x, xs') = xs in
                    x - 1.
                |]
      parse P.decl "decl4" (unpack tc4) `shouldBe`
        Right (Decl (TyNat `TyArr` TyStream "foo" `TyArr` "foo") "foo"
              ("a" --> "xs" --> tmlet (PCons "x" "xs'") "xs" $ "x" - 1))

    describe "forall f in TestFunctions.frps. parse (ppshow f) = f" $ do
      mapM_ (\d -> it ("is true for " ++ _name d) $
        let e = parse P.decl ("decl_" ++ _name d) (ppshow d)
        in case e of
          Right r -> r `shouldBe` d
          Left e  -> fail (ppshow d ++ "\n" ++ show e)) frps

  describe "program parsing" $ do
    it "should work with const program" $ do
      let p = [text|
              const : S alloc -> Nat -> S Nat
              const us n =
                let cons(u, us') = us in
                let stable(x) = n in
                cons(x, delay(u, const us' x)).

              main : S alloc -> S Nat
              main us = const us 10.
              |]
      let Right r = parse P.prog "const" $ unpack p
      r `shouldBe`
        Program
          { _main = Decl
            { _type = TyArr (TyStream TyAlloc) (TyStream TyNat)
            , _name = "main"
            , _body = tmlam "us" (tmapp (tmapp (tmvar "const") (tmvar "us")) (tmlit (LInt 10)))
            }
          , _decls =
            [ Decl
                { _type = TyArr (TyStream TyAlloc) (TyArr TyNat (TyStream TyNat))
                , _name = "const"
                , _body =
                    tmlam "us" (tmlam "n"
                      (tmlet (PCons (PBind "u") (PBind "us'")) (tmvar "us")
                      (tmlet (PStable (PBind "x")) (tmvar "n")
                      (tmcons (tmvar "x")
                        (tmdelay (tmvar "u") (tmapp (tmapp (tmvar "const") (tmvar "us'")) (tmvar "x")))
                      ))))
                }
            ]
          }
    it "should work with sum program" $ do
      let p = [text|
              nats : S alloc -> S Nat
              nats us n =
                let cons(u, delay(us')) = us in
                let stable(x) = promote(n) in
                cons(x, delay(u, nats us' (x + 1))).

              sum_acc : S alloc -> S Nat -> Nat -> S Nat
              sum_acc us ns acc =
                let cons(u, delay(us')) = us in
                let cons(n, delay(ns')) = ns in
                let stable(x) = promote(n + acc) in
                cons(x, delay(u, sum_acc us' ns' x)).

              sum : S alloc -> S Nat -> S Nat
              sum us ns =
                sum_acc us ns 0.

              main : S alloc -> S Nat
              main us =
                sum us nats us 0.
              |]
      let Right r = parse P.prog "sum" $ unpack p
      let exp = Program
            { _main = Decl
              { _type = TyArr (TyStream TyAlloc) (TyStream TyNat)
              , _name = "main"
              , _body = tmlam "us"
                          (tmapp
                             (tmapp
                                (tmapp (tmapp (tmvar "sum") (tmvar "us")) (tmvar "nats"))
                                (tmvar "us"))
                             (tmlit (LInt 0)))
              }
            , _decls = [ Decl
                         { _type = TyArr (TyStream TyAlloc) (TyStream TyNat)
                         , _name = "nats"
                         , _body = tmlam "us"
                                     (tmlam "n"
                                        (tmlet
                                           (PCons (PBind "u") (PDelay "us'"))
                                           (tmvar "us")
                                           (tmlet
                                              (PStable (PBind "x"))
                                              (tmpromote (tmvar "n"))
                                              (tmcons (tmvar "x")
                                                 (tmdelay (tmvar "u")
                                                    (tmapp
                                                       (tmapp (tmvar "nats") (tmvar "us'"))
                                                       (tmbinop Add (tmvar "x")
                                                          (tmlit (LInt 1)))))))))
                         }
                       , Decl
                         { _type = TyArr (TyStream TyAlloc)
                                     (TyArr (TyStream TyNat)
                                        (TyArr TyNat (TyStream TyNat)))
                         , _name = "sum_acc"
                         , _body = tmlam "us"
                                     (tmlam "ns"
                                        (tmlam "acc"
                                           (tmlet
                                              (PCons (PBind "u") (PDelay "us'"))
                                              (tmvar "us")
                                              (tmlet
                                                 (PCons (PBind "n") (PDelay "ns'"))
                                                 (tmvar "ns")
                                                 (tmlet
                                                    (PStable (PBind "x"))
                                                    (tmpromote
                                                       (tmbinop Add (tmvar "n")
                                                          (tmvar "acc")))
                                                    (tmcons (tmvar "x")
                                                       (tmdelay (tmvar "u")
                                                          (tmapp
                                                             (tmapp
                                                                (tmapp (tmvar "sum_acc")
                                                                   (tmvar "us'"))
                                                                (tmvar "ns'"))
                                                             (tmvar "x")))))))))
                         }
                       , Decl
                         { _type = TyArr (TyStream TyAlloc)
                                     (TyArr (TyStream TyNat) (TyStream TyNat))
                         , _name = "sum"
                         , _body = tmlam "us"
                                     (tmlam "ns"
                                        (tmapp
                                           (tmapp (tmapp (tmvar "sum_acc") (tmvar "us"))
                                              (tmvar "ns"))
                                           (tmlit (LInt 0))))
                         }
                       ]
            }
      r `shouldBe` exp







