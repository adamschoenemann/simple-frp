
module FRP.Generators where

import           FRP.AST
import           FRP.AST.Construct
import           Test.QuickCheck


type TestTerm = Term ()

genInt :: Gen TestTerm
genInt = tmlit . LInt <$> arbitrary

genBool :: Gen TestTerm
genBool = tmlit . LBool <$> arbitrary

genVar :: Gen TestTerm
genVar = tmvar <$> (elements . (:[]) $ ['a'..'z'])

genSimpleTerm :: Gen TestTerm
genSimpleTerm = oneof [genVar, genBool, genInt]
