
module FRP.Generators where

import           Control.Monad     (replicateM)
import           FRP.AST
import           FRP.AST.Construct
import           Test.QuickCheck


type TestTerm = Term ()

genInt :: Gen TestTerm
genInt = tmlit . LInt <$> arbitrary

genBool :: Gen TestTerm
genBool = tmlit . LBool <$> arbitrary

genName :: Gen String
genName = (:[]) <$> elements ['a'..'z']

genVar :: Gen TestTerm
genVar = tmvar <$> genName

genSimpleTerm :: Gen TestTerm
genSimpleTerm = oneof [genVar, genBool, genInt]

genOps :: Gen TestTerm -> Int -> Gen TestTerm
genOps termGen = go where
  go n = do
    m <- choose (0, n)
    if (m == 0)
      then termGen
      else do
        op <- elements [eq, (+), (-), (>.), (<.), (<==), (>==), (*), tmbinop Div]
        left <- go (div n (m + 1))
        right <- go (div n (m + 1))
        return $ op left right

genLam :: Gen TestTerm -> Int -> Gen TestTerm
genLam termGen = go where
  go n = do
    m <- choose (0, n)
    nm <- genName
    bd <- if (m == 0) then termGen else go (div n (m + 1))
    return (nm --> bd)

genApp :: Gen TestTerm -> Int -> Gen TestTerm
genApp termGen = go where
  go n = do
    m <- choose (0, n)
    if (m == 0)
      then termGen
      else do
        lam <- genLam termGen 1 -- (div n (m + 1))
        app <- go (div n (m + 1))
        return (lam <| app)

genFst :: Gen TestTerm -> Gen TestTerm
genFst termGen = tmfst <$> termGen

genSnd :: Gen TestTerm -> Gen TestTerm
genSnd termGen = tmsnd <$> termGen

genPat :: Int -> Gen Pattern
genPat n = do
  m <- choose (0, n)
  if (m == 0)
    then do
      nm <- genName
      elements [PBind nm, PDelay nm]
    else do
      p1 <- genPat (div n (m + 1))
      p2 <- genPat (div n (m + 1))
      elements [PCons p1 p2, PStable p1, PTup p1 p2]

genLet :: Gen TestTerm -> Int -> Gen TestTerm
genLet termGen = go where
  go n = do
    m <- choose (0, n)
    if (m == 0)
      then termGen
      else let m1 = (div n (m + 1))
           in tmlet <$> genPat m1 <*> termGen <*> go m1
        -- pat <- genPat (div n (m + 1))
        -- rhs <- termGen
        -- next <- go (div n (m + 1))
        -- return $ tmlet pat rhs next


