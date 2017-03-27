{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes       #-}

module FRP.ParserSpec where

import           FRP.AST
import           FRP.AST.Construct
import qualified FRP.Parser.Decl     as P
import qualified FRP.Parser.Program  as P
import qualified FRP.Parser.Term     as P
import qualified FRP.Parser.Type     as P
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
import           FRP.Generators
import           FRP.TestFunctions   (frps, frp_unfold)
import           Test.QuickCheck



txt_frp_nats =
  [text|
  \n us ->
    let cons(u, delay(us')) = us in
    let stable(x) = promote(n) in
    cons(x, delay (u, const us' (x + 1)))
  |]

txt_frp_const =
  [text|
  \n us ->
    let cons(u, delay(us')) = us in
    let stable(x) = promote(n) in
    cons(x, delay (u, const us' x))
  |]

txt_frp_sum_acc =
  [text|
  \us ns acc ->
    let cons(u, delay(us')) = us in
    let cons(n, delay(ns')) = ns in
    let stable(x) = promote(n + acc) in
    cons(x, delay(u, sum_acc us' ns' x))
  |]

txt_frp_map =
  [text|
  \us h xs ->
    let cons(u, delay(us')) = us in
    let cons(x, delay(xs')) = xs in
    let stable(f)           = h  in
    cons(f x, delay(u, map us' stable(f) xs'))
  |]

txt_frp_swap =
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

txt_frp_switch =
  [text|
  \us xs e ->
    let cons(u, delay(us')) = us in
    let cons(x, delay(xs')) = xs in
    case out e of
      | inl ys -> ys
      | inr t  -> let delay(e') = t in
                  cons(x, delay (u, switch us' xs' e')))
  |]

txt_frp_bind =
  [text|
  \us -> \h -> \e ->
    let cons(u, delay(us')) = us in
    let stable(f)           = h  in
    case out e of
      | inl a -> f a
      | inr t -> let delay(e') = t in
                 into (inr (delay (u, bind us' stable(f) e')))
  |]

main :: IO ()
main = hspec spec

shouldParse :: (Eq (f ()), Show (f ()), Functor f) => Either ParseError (f a) -> f () -> Expectation
shouldParse eith expect = case eith of
  Left err  -> expectationFailure (show err)
  Right ast -> unitFunc ast `shouldBe` expect

spec :: Spec
spec = do
  describe "term parsing" $ do
    it "should parse lambda expressions" $ do
      parse P.tmlam "lam" "\\x -> x" `shouldParse` ("x" --> "x")
      parse P.term "lam" "\\x  -> x" `shouldParse` ("x" --> "x")
      parse P.term "lam" "\\x  -> x + x" `shouldParse`
        ("x" --> ("x" + "x"))

      parse P.term "lam" "\\x -> \\y -> x + y" `shouldParse`
        ("x" --> "y" --> ("x" + "y"))

      parse P.term "lam1" "\\x y z -> y" `shouldParse`
        ("x" --> "y" --> "z" --> "y")

    it "should parse lambdas with types" $ do
      parse P.term "lamty" "\\(x:Nat) -> x" `shouldParse`
        tmlamty "x" tynat "x"
      parse P.term "lamty" "\\(x:Nat) -> \\(y:Bool) -> x" `shouldParse`
        tmlamty "x" tynat (tmlamty "y" (tybool) "x")

      parse P.term "lamty" "\\(x:Nat) (y:Bool) -> x" `shouldParse`
        tmlamty "x" tynat (tmlamty "y" (tybool) "x")

      parse P.term "lamty" "\\(x:Nat -> S Bool) (y : Nat * Bool) -> x" `shouldParse`
        tmlamty "x" (tynat |-> TyStream () tybool)
          (tmlamty "y" (tynat .*. tybool) "x")

    it "should parse let expressions" $ do
      parse P.tmlet "let" "let x = 10 in x" `shouldParse`
        (tmlet "x" 10 "x")
      parse P.term "let" "let x = 10 in x" `shouldParse`
        (tmlet "x" 10 "x")
      parse P.term "let" "let x = y in\n x * y" `shouldParse`
        (tmlet "x" "y" ("x" * "y"))
      parse P.term "let" "let x = 10 in let y = 42 in x * y" `shouldParse`
        (tmlet "x" 10 $ tmlet "y" 42 ("x" * "y"))

      -- should still work if we change the var names
      parse P.term "let" "let outro = 10 in let y = 42 in outro * y" `shouldParse`
        (tmlet "outro" 10 $ tmlet "y" 42 ("outro" * "y"))

      parse P.term "let" "10 + let x = 10 in let y = 42 in x * y" `shouldParse`
        (10 + (tmlet "x" 10 $ tmlet "y" 42 ("x" * "y")))

    it "should parse cons expressions" $ do
      parse P.tmcons "cons" "cons(10, 20)" `shouldParse`
        (tmcons 10 20)
      parse P.tmcons "cons" "cons ( 10  , 20  )  " `shouldParse`
        (tmcons 10 20)
      parse P.term "term" "cons(10, 20)" `shouldParse`
        (tmcons 10 20)
      parse P.term "term" "cons ( 10  , 20  )  " `shouldParse`
        (tmcons 10 20)

    it "should parse tuples" $ do
      parse P.term "tup1" "(x,y)" `shouldParse` (tmtup "x" "y")
      parse P.term "tup2" "(x,(y, x+y))" `shouldParse` (tmtup "x" (tmtup "y" ("x" + "y")))
      parse P.term "tup3" "fst (x,y) * 20" `shouldParse`
        ((tmfst (tmtup "x" "y")) * 20)

    it "should parse tuple projections" $ do
      parse P.term "fst" "\\y -> let x = fst y in x * 10" `shouldParse`
        ("y" --> tmlet "x" (tmfst "y") $ "x" * 10)
      parse P.term "snd" "\\y -> let x = snd y in x * 10" `shouldParse`
        ("y" --> tmlet "x" (tmsnd "y") $ "x" * 10)

      parse P.term "snd and fst" "\\z -> let x = fst z in let y = snd z in x * y" `shouldParse`
        ("z" --> tmlet "x" (tmfst "z") $ tmlet "y" (tmsnd "z") $ "x" * "y")

    it "parses application" $ do
      parse P.term "app" "x x" `shouldParse`
        ("x" <| "x")

      parse P.term "app" "\\x -> let y = 10 in x (y * 2)" `shouldParse`
        ("x" --> tmlet "y" 10 $ "x" <| ("y" * 2))

      parse P.term "app" "\\f -> let x = f x in x" `shouldParse`
        ("f" --> tmlet "x" ("f" <| "x") "x")

      parse P.term "app" "10 + (\\x -> x * 2) 4" `shouldParse`
        (10 + ("x" --> "x" * 2) <| 4)

      let nestedApp = "f x (f y) (h (g x) f y)"
      let nestedAppExp =
            ("f" <| "x" <| ("f" <| "y") <| ("h" <| ("g" <| "x") <| "f" <| "y"))

      parse P.term "app" nestedApp `shouldParse` nestedAppExp

      parse P.term "app" (ppshow nestedAppExp) `shouldParse` nestedAppExp

    it "parses fixpoint" $ do
      parse P.term "fix" "fix (x:Nat). x" `shouldParse`
        (tmfix "x" tynat "x")

      parse P.term "fix" "fix (f:Nat). (\\x y -> x)" `shouldParse`
        (tmfix "f" tynat $ "x" --> "y" --> "x")

      parse P.term "fix" "fix (f:Nat -> Nat). (\\x -> if x < 0 then 0 else f (x - 1))" `shouldParse`
        (tmfix "f" (tynat |-> tynat) $ "x" --> tmite ("x" <. 0) 0 ("f" <| ("x" - 1)))

    it "parses nested patterns" $ do
      parse P.term "pats" "let cons(u, delay(us')) = us in u" `shouldParse`
        (tmlet (PCons "u" (PDelay "us'")) "us" "u")

    it "parses if-then-else" $ do
      parse P.tmite "ite" "if x == 10 then True else False" `shouldParse`
        (tmite ("x" `eq` 10) (tmbool True) (tmbool False))

      parse P.term "ite" "if x == 10 then True else False" `shouldParse`
        (tmite ("x" `eq` 10) (tmbool True) (tmbool False))

      parse P.term "ite" "if x > 10 then x + 10 else x == 20" `shouldParse`
        (tmite ("x" >. 10)
                     ("x" + 10)
                     ("x" `eq` 20)
              )

      parse P.term "ite" "42 + if x > 10 then x + 10 else x == 20" `shouldParse`
        (42 + tmite ("x" >. 10)
                     ("x" + 10)
                     ("x" `eq` 20)
              )

    it "parses case exprs" $ do
      parse P.tmcase "case 1" "case x of | inl y -> 10 | inr z -> 20" `shouldParse`
        (tmcase "x" ("y", 10) ("z", 20))

      parse P.term "case 2" "10 + case x of | inl y -> 10 | inr z -> 4 + 1" `shouldParse`
        (10 + tmcase "x" ("y", 10) ("z", 4 + 1))

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
      parse P.term "nested case" (unpack nested_case) `shouldParse`
        (tmcase "x"
                ("y", tmcase "y" ("yy", "yy" * 10) ("yz", "yz" - 10))
                ("z", tmcase "z" ("zy", "zy" * 10) ("zz", "zz" + 10))
              )

    it "parses compound expressions" $ do
      parse P.term "frp" "\\x -> \\y -> let z = x + y in cons(x, z * x + y)" `shouldParse`
        ("x" --> "y" --> tmlet "z" ("x" + "y") $ tmcons "x" ("z" * "x" + "y"))

      parse P.term "frp" "let y = 2 * 10 in (\\x -> 2 * x) (y + 2)" `shouldParse`
        (tmlet "y" (2 * 10) $ ("x" --> 2 * "x") <| ("y" + 2))

      let txt_frp_const_ast =
            "n" --> "us" -->
              tmlet (PCons "u" (PDelay "us'")) "us" $
              tmlet (PStable "x") (tmpromote "n") $
              tmcons "x" (tmdelay "u" $ "const" <| "us'" <| "x")

      parse P.term "txt_frp_const" (unpack txt_frp_const) `shouldParse` (txt_frp_const_ast)

      let txt_frp_sum_acc_ast =
            "us" --> "ns" --> "acc" -->
              tmlet (PCons "u" (PDelay "us'")) "us" $
              tmlet (PCons "n" (PDelay "ns'")) "ns" $
              tmlet (PStable "x") (tmpromote ("n" + "acc")) $
              tmcons "x" (tmdelay "u" ("sum_acc" <| "us'" <| "ns'" <| "x"))

      parse P.term "txt_frp_sum_acc" (unpack txt_frp_sum_acc) `shouldParse` (txt_frp_sum_acc_ast)

      let txt_frp_map_ast =
            "us" --> "h" --> "xs" -->
              tmlet (PCons "u" (PDelay "us'")) "us" $
              tmlet (PCons "x" (PDelay "xs'")) "xs" $
              tmlet (PStable "f") "h" $
              tmcons ("f" <| "x")
                     (tmdelay "u" ("map" <| "us'" <| tmstable "f" <| "xs'"))

      parse P.term "txt_frp_map" (unpack txt_frp_map) `shouldParse` (txt_frp_map_ast)

      let txt_frp_swap_ast =
            "us" --> "n" --> "xs" --> "ys" -->
              tmite ("n" `eq` 0) "ys" $
                tmlet (PCons "u" (PDelay "us'")) "us" $
                tmlet (PCons "x" (PDelay "xs'")) "xs" $
                tmlet (PCons "y" (PDelay "ys'")) "ys" $
                tmlet (PStable "m") (tmpromote "n") $
                tmcons "x"
                       (tmdelay "u" $ "swap" <| "us'" <|
                                      ("m" - 1) <| "xs'" <| "ys'"
                       )

      parse P.term "txt_frp_swap" (unpack txt_frp_swap) `shouldParse` (txt_frp_swap_ast)

      let txt_frp_switch_ast =
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

      parse P.term "txt_frp_switch" (unpack txt_frp_switch) `shouldParse` (txt_frp_switch_ast)

      let txt_frp_bind_ast =
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

      parse P.term "txt_frp_bind" (unpack txt_frp_bind) `shouldParse` (txt_frp_bind_ast)

    it "parses negative numbers" $ do
      parse P.term "neg" "-(10)" `shouldParse` (tmlit (LInt (-10)))
      parse P.term "neg" "10 * -(10)" `shouldParse` (10 * (tmlit (LInt (-10))))

  describe "type parsing" $ do
    it "parses Nat" $ do
      parse P.ty "nat" "Nat" `shouldParse` tynat
    it "parses alloc" $ do
      parse P.ty "alloc" "alloc" `shouldParse` tyalloc
    it "parses streams" $ do
      parse P.ty "stream of nats" "S Nat" `shouldParse`
        (tystream tynat)
      parse P.ty "stream of allocs" "S alloc" `shouldParse`
        (tystream tyalloc)
      parse P.ty "stream of params" "S a" `shouldParse`
        (tystream $ tyvar "a")
      parse P.ty "stream of params" "S s" `shouldParse`
        (tystream $ tyvar "s")
      parse P.ty "stream of params" "S Sample" `shouldParse`
        (tystream $ tyvar "Sample")
    it "parses products" $ do
      parse P.ty "pair of nats" "Nat * Nat" `shouldParse`
        (typrod tynat tynat)
      parse P.ty "pair of nat x alloc" "Nat * alloc" `shouldParse`
        (typrod tynat tyalloc)
      parse P.ty "pair of params" "a * b" `shouldParse`
        (typrod (tyvar "a") (tyvar "b"))
      parse P.ty "pair of streams of nats" "S Nat * S Nat" `shouldParse`
        (typrod (tystream tynat) (tystream tynat))
      parse P.ty "nested pair" "Nat * Nat * Nat" `shouldParse`
        (typrod tynat (typrod tynat tynat))
    it "parses sums" $ do
      parse P.ty "sum of nats" "Nat + Nat" `shouldParse`
        (tysum tynat tynat)
      parse P.ty "sum of nat x alloc" "Nat + alloc" `shouldParse`
        (tysum tynat tyalloc)
      parse P.ty "sum of params" "a + b" `shouldParse`
        (tysum (tyvar "a") (tyvar "b"))
      parse P.ty "sum of streams of nats" "S Nat + S Nat" `shouldParse`
        (tysum (tystream tynat) (tystream tynat))
      parse P.ty "nested sum" "Nat + Nat + Nat" `shouldParse`
        (tysum tynat (tysum tynat tynat))
    it "parses arrows" $ do
      parse P.ty "arrow of nats" "Nat -> Nat" `shouldParse`
        (tynat |-> tynat)
      parse P.ty "arrow of nat x alloc" "Nat -> alloc" `shouldParse`
        (tynat |-> tyalloc)
      parse P.ty "arrow of params" "a -> b" `shouldParse`
        (tyvar "a" |-> tyvar "b")
      parse P.ty "arrow of streams of nats" "S Nat -> S Nat" `shouldParse`
        (tystream tynat |-> tystream tynat)
      parse P.ty "nested arrows" "Nat -> Nat -> Nat" `shouldParse`
        (tynat |-> tynat |-> tynat)
    it "parses later" $ do
      parse P.ty "later Nat" "@Nat" `shouldParse`
        (tylater tynat)
      parse P.ty "later Alloc" "@alloc" `shouldParse`
        (tylater tyalloc)
      parse P.ty "later S Alloc" "@(S alloc)" `shouldParse`
        (tylater $ tystream tyalloc)
      parse P.ty "later Nat -> Nat" "@(Nat -> Nat)" `shouldParse`
        (tylater (tynat |-> tynat))
      parse P.ty "later Nat * Nat" "@(Nat * Nat)" `shouldParse`
        (tylater $ typrod tynat tynat)
    it "parses stable" $ do
      parse P.ty "stable Nat" "#Nat" `shouldParse`
        (tystable tynat)
      parse P.ty "stable Alloc" "#alloc" `shouldParse`
        (tystable tyalloc)
      parse P.ty "stable S Alloc" "#(S alloc)" `shouldParse`
        (tystable $ tystream tyalloc)
      parse P.ty "stable Nat -> Nat" "#(Nat -> Nat)" `shouldParse`
        (tystable (tynat |-> tynat))
      parse P.ty "stable Nat * Nat" "#(Nat * Nat)" `shouldParse`
        (tystable $ typrod tynat tynat)
    it "parses compund types" $ do
      parse P.ty "c1" "S Nat -> #(S A) -> X" `shouldParse`
        (tystream tynat |-> tystable (tystream "A") |-> "X")
      parse P.ty "map" "S alloc -> #(A -> B) -> S A -> S B" `shouldParse`
        (tystream tyalloc |-> tystable ("A" |-> "B") |->
               tystream "A" |-> tystream "B")
      parse P.ty "tails" "S alloc -> S A -> S (S A)" `shouldParse`
        (tystream tyalloc |-> tystream "A" |-> tystream (tystream "A"))
      parse P.ty "unfold" "S alloc -> #(X -> A * @X) -> X -> S A" `shouldParse`
        (tystream tyalloc |->
               tystable ("X" |-> typrod "A" (tylater "X")) |->
               "X" |->
               tystream "A"
              )
  describe "parsing declarations" $ do
    it "should parse simple decls1" $ do
      let tc1 = [text|
                 foo : Nat
                 foo = 5.
                |]
      parse P.decl "decl1" (unpack tc1) `shouldParse`
        (Decl () (tynat) "foo" 5)

    it "should parse simple decls2" $ do
      let tc2 = [text|
                 foo : Nat -> Nat
                 foo = \x -> x.
                |]
      parse P.decl "decl2" (unpack tc2) `shouldParse`
        (Decl () (tynat |-> tynat) "foo" (tmlam "x" "x"))

    it "should parse simple decls3" $ do
      let tc3 = [text|
                 foo : Nat -> S a -> a

                    foo = \a -> \xs ->
                            let cons(x, xs') = xs in
                            x - 1.
                |]
      parse P.decl "decl3" (unpack tc3) `shouldParse`
        (Decl () (tynat |-> tystream "a" |-> "a") "foo"
              ("a" --> "xs" --> tmlet (PCons "x" "xs'") "xs" $ "x" - 1))

    it "should parse simple decls4" $ do
      let tc4 = [text|
                 foo : Nat -> S foo -> foo

                    foo = \a -> \xs ->
                            let cons(x, xs') = xs in
                            x - 1.
                |]
      parse P.decl "decl4" (unpack tc4) `shouldParse`
        (Decl () (tynat |-> tystream "foo" |-> "foo") "foo"
              ("a" --> "xs" --> tmlet (PCons "x" "xs'") "xs" $ "x" - 1))

    it "should parse with param list" $ do
      let tc4 = [text|
                 foo : Nat -> S foo -> foo
                 foo a xs =
                    let cons(x, xs') = xs in
                    x - 1.
                |]
      parse P.decl "decl4" (unpack tc4) `shouldParse`
        (Decl () (tynat |-> tystream "foo" |-> "foo") "foo"
              ("a" --> "xs" --> tmlet (PCons "x" "xs'") "xs" $ "x" - 1))

    describe "forall f in TestFunctions.frps. parse (ppshow f) = f" $ do
      mapM_ (\d -> it ("is true for " ++ _name d) $
        let e = parse P.decl ("decl_" ++ _name d) (ppshow d)
        in case e of
          Right r -> unitFunc r `shouldBe` d
          Left e  -> fail (ppshow d ++ "\n" ++ show e)) frps

  describe "program parsing" $ do
    -- it "should work with unfold program" $ do
    --   txt_frp_unfold `shouldBe` txt_frp_unfold'

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
      let constTy = tyarr (tystream tyalloc) (tyarr tynat (tystream tynat))
      unitFunc r `shouldBe`
        Program
          { _decls =
            [ Decl
                { _ann  = ()
                , _type = constTy
                , _name = "const"
                , _body =
                    tmfix "const" constTy $ tmlam "us" (tmlam "n"
                      (tmlet (PCons (PBind "u") (PBind "us'")) (tmvar "us")
                      (tmlet (PStable (PBind "x")) (tmvar "n")
                      (tmcons (tmvar "x")
                        (tmdelay (tmvar "u") (tmapp (tmapp (tmvar "const") (tmvar "us'")) (tmvar "x")))
                      ))))
                }

            , Decl
              { _ann  = ()
              , _type = tyarr (tystream tyalloc) (tystream tynat)
              , _name = "main"
              , _body = tmlam "us" (tmapp (tmapp (tmvar "const") (tmvar "us")) (tmlit (LInt 10)))
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
      let sumTy = tyarr (tystream tyalloc)
                        (tyarr (tystream tynat)
                        (tyarr tynat (tystream tynat)))
      let natTy = tyarr (tystream tyalloc) (tystream tynat)
      let exp = Program
            { _decls = [ Decl
                         { _ann  = ()
                         , _type = natTy
                         , _name = "nats"
                         , _body = tmfix "nats" natTy $ tmlam "us"
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
                         { _ann  = ()
                         , _type = sumTy
                         , _name = "sum_acc"
                         , _body = tmfix "sum_acc" sumTy $ tmlam "us"
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
                         { _ann  = ()
                         , _type = tyarr (tystream tyalloc)
                                     (tyarr (tystream tynat) (tystream tynat))
                         , _name = "sum"
                         , _body = tmlam "us"
                                     (tmlam "ns"
                                        (tmapp
                                           (tmapp (tmapp (tmvar "sum_acc") (tmvar "us"))
                                              (tmvar "ns"))
                                           (tmlit (LInt 0))))
                         }
                       , Decl
                          { _ann  = ()
                          , _type = tyarr (tystream tyalloc) (tystream tynat)
                          , _name = "main"
                          , _body = tmlam "us"
                                      (tmapp
                                         (tmapp
                                            (tmapp (tmapp (tmvar "sum") (tmvar "us")) (tmvar "nats"))
                                            (tmvar "us"))
                                         (tmlit (LInt 0)))
                          }
                       ]
            }
      unitFunc r `shouldBe` exp

    it "should work with QuickCheck (1)" $ property $ forAll (genOps genSimpleTerm 10) $
      \p -> parse P.term (ppshow p) (ppshow p) `shouldParse` p

    it "should work with QuickCheck (2)" $ property $ forAll (genLam (genOps genSimpleTerm 5) 10) $
      \p -> parse P.term (ppshow p) (ppshow p) `shouldParse` p

    -- it "should work with QuickCheck (3)" $ do
    --   xs <- sample' (genApp (genOps genSimpleTerm 1) 1)
    --   let fn e = let Right r = parse P.term "" (ppshow e)
    --              in  replicate 20 '=' ++ "\n" ++ ppshow e ++ "\n\n" ++
    --                  ppshow (unitFunc r) ++ "\n"
    --   mapM_ (putStrLn . fn) xs

    -- -- doesn't work atm
    -- it "should work with QuickCheck (3)" $ property $ forAll (genApp (genOps genSimpleTerm 1) 1) $
    --   \p -> do ppputStrLn p; parse P.term "quickcheck 3" (ppshow p) `shouldParse` p


    it "should work with QuickCheck (4)" $ property $ forAll (genLet (genOps genSimpleTerm 1) 1) $
      \p -> parse P.term (ppshow p) (ppshow p) `shouldParse` p






