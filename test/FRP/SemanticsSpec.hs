
module FRP.SemanticsSpec where

import           FRP.AST
import           FRP.AST.Construct
import           FRP.Pretty
import           FRP.Semantics
import           Test.Hspec

import           Control.Monad.State
import           Data.List           (unfoldr)
import qualified Data.Map.Strict     as M
import           Debug.Trace

import           FRP.TestFunctions

main :: IO ()
main = hspec spec

ppdebug :: Pretty p => p -> IO ()
-- ppdebug = ppputStrLn
ppdebug = const (return ())

debug :: String -> IO ()
-- debug = putStrLn
debug = const (return ())

spec :: Spec
spec = do
  describe "operational semantics" $ do
    describe "function application" $ do
      it "works with a simple function" $ do
        let term = ("x" --> "x") <| 10
        -- ppdebug term
        let r = evalExpr noInputs M.empty term
        r `shouldBe` VLit (LNat 10)
      it "works with two arguments" $ do
        let term = ("x" --> "y" --> "x" + "y") <| 10 <| 5
        -- ppdebug term
        let r = evalExpr noInputs M.empty term
        r `shouldBe` VLit (LNat 15)
        -- ppdebug r
      it "adds a nested vars to scope" $ do
        let lam = "x" --> "y" --> "x" <| "y"
        let app = lam <| ("z" --> 10 + "z")
        let term = app <| 5
        -- debug . ppshow $ term
        let r = evalExpr noInputs M.empty term
        r `shouldBe` VLit (LNat 15)
        -- debug $ "result: " ++ (ppshow r)
      it "does not capture free variables" $ do
        let l1 = ("x" --> "y" --> "z" --> "x" <| ("y" + "z")) <|
                 ("y" --> "y" + 42)
        let term = l1 <| 6 <| 4
        let r = evalExpr noInputs M.empty term
        r `shouldBe` VLit (LNat 52)
        -- debug $ "result: " ++ (ppshow r)
    describe "fixpoint" $ do
      it "works for const" $ do
        let fp = tmfix "x" tynat ("y" --> "y") <| 10
        let v = evalExpr noInputs M.empty fp
        v `shouldBe` (VLit (LNat 10))
        -- ppdebug v
      it "works for factorial" $ do
        let fact = tmfix "f" (tynat |-> tynat) ("n" --> tmite ("n" `eq` 1) 1 ("n" * ("f" <| ("n" - 1))))
        -- ppdebug fact
        let v = evalExpr noInputs M.empty (fact <| 4)
        v `shouldBe` (VLit (LNat 24))
        -- ppdebug v
      it "works for fibonacci" $ do
        let fib = tmfix "f" (tynat |-> tynat |-> tynat) $ "n" -->
                    tmite ("n" <== 1)
                      "n"
                      ("f" <| ("n" - 1) + "f" <| ("n" - 2))
        -- ppdebug fib
        let v = evalExpr noInputs M.empty (fib <| 7)
        v `shouldBe` (VLit (LNat 13))
        -- ppdebug v

    describe "fixedpoint" $ do
      it "works with stream of allocators" $ do
        let fp = tmfix "xs" undefined $ tmcons tmalloc (tmdelay tmalloc "xs")
        let run s e n =
              let (v, s')  = runExpr s noInputs M.empty e
                  VCons _ (VPntr l) = v
              in  if n >= 10 then return () else do
                     v `shouldBe` VCons VAlloc (VPntr n)
                     run (tick noInputs s') (tmpntrderef l) (n+1)

        r <- run initialState fp 0
        r `shouldBe` ()

    describe "streams" $ do
      it "works with const" $ do
        let constfn =
              "us" --> "n" -->
                tmlet (PCons "u" (PDelay "us'")) "us" $
                tmlet (PStable "x") (tmpromote "n") $
                tmcons "x" (tmdelay "u" ("const" <| "us" <| "x"))
        let mainbd = "us" --> "const" <| "us" <| 10
        let mainfn = Decl () undefined "main" mainbd
        let prog = Program [] [mainfn, Decl () undefined "const" constfn]
        take 100 (interpProgram prog) `shouldBe` map (VLit . LNat) (replicate 100 10)
        -- debug $ show $ interpProgram prog
      it "works with nats" $ do
        let mainbd = "us" --> "nats" <| "us" <| 0
        let mainfn = frp_main mainbd (tystream tynat)
        let prog = Program [] [mainfn, frp_nats]
        take 100 (interpProgram prog) `shouldBe` map (VLit . LNat) [0..99]
      it "works with sum" $ do
        let prog = prog_sum
        take 100 (interpProgram prog) `shouldBe` map (VLit . LNat) (scanl (+) 0 [1..99])

        ppdebug frp_sum_acc
        debug ""
        let (v, s) = stepProgram prog
        debug "======== run 1 ======="
        ppdebug v
        ppdebug s
        let VCons _ (VPntr l) = v
        let (v', s') = runExpr (tick noInputs s) noInputs M.empty (tmpntrderef l)
        debug "======== run 2 ======="
        ppdebug v'
        ppdebug s'
        let VCons _ (VPntr l') = v'
        let (v'', s'') = runExpr (tick noInputs s') noInputs M.empty (tmpntrderef l')
        debug "======== run 3 ======="
        ppdebug v''
        ppdebug s''
        debug . show $ take 500 (interpProgram prog)
      it "works with tails" $ do

        -- ppdebug frp_tails
        -- debug ""
        let prog = prog_tails
        let k = 10
        let got = take k $ map (take k . toHaskList) (interpProgram prog)
        let expect = map (\n -> map (VLit . LNat) [n..(n+k-1)]) [1..k]
        got `shouldBe` expect

      it "works with map" $ do
        let prog = prog_map
        let k = 100
        let got = take k $ (interpProgram prog)
        -- mapM_ (debug . show) got
        let expect = map (VLit . LNat . (* 2)) [0..k-1]
        got `shouldBe` expect

      it "works with unfold (nats)" $ do
        let prog = prog_unfold
        let k = 50
        let got = take k $ (interpProgram prog)
        -- mapM_ (debug . show) got
        let expect = map (VLit . LNat) $ [0..k-1]
        got `shouldBe` expect

        -- old fibs expectation
        -- take k $ unfoldr (\(a,b) -> Just (a+b, (b,a+b))) (0,1)

      it "works with swap 10 nats (const 42)" $ do
        let prog = prog_swap_const_nats
        let k = 50
        let got = take k $ (interpProgram prog)
        -- mapM_ (debug . show) got
        -- let fibs = unfoldr (\(a,b) -> Just (a+b, (b,a+b))) (0,1)
        let expect = map (VLit . LNat) $ [0..9] ++ take (k-10) (repeat 42)
        got `shouldBe` expect


    describe "tick" $ do
      let mkStore s = EvalState s 0
      it "sats tick [] = []" $ do
        tick noInputs initialState `shouldBe` initialState
      it "sats tick [l : v now] = []" $ do
        tick noInputs (mkStore M.empty) `shouldBe` initialState
      it "sats tick [l : e later] = [l : v now]" $ do
        let s  = M.singleton 0 $ SVLater 10 M.empty
        let s' = M.singleton 0 $ SVNow   (VLit  $ LNat 10)
        tick noInputs (mkStore $ s) `shouldBe` mkStore s'
      it "sats tick [l1 : v now, l2 : e later] = [l2 : v' now]" $ do
        let s  = M.insert 0 (SVNow (VLit $ LNat 1)) $ M.singleton 1 $ SVLater 10 M.empty
        let s' = M.singleton 1 $ SVNow  (VLit $ LNat 10)
        tick noInputs (mkStore $ s) `shouldBe` mkStore s'
      it "sats tick [0 : e later, 1 : *0 later, 2 : v now] = [0 : v now, 1 : v now]" $ do
        let s  = M.insert 0 (SVLater 1 M.empty) $ M.insert 1 (SVLater (tmpntrderef 0) M.empty) $ M.singleton 2 (SVNow (VLit $ LNat 42))
        let s' = M.insert 0 (SVNow (VLit $ LNat 1)) $ M.singleton 1 $ SVNow (VLit $ LNat 1)
        tick noInputs (mkStore $ s) `shouldBe` mkStore s'

    -- TODO: Test inputs