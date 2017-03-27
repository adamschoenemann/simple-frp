
module FRP.AST.QuasiQuoter where

import qualified FRP.Parser.Program as P
import qualified FRP.Parser.Decl    as P
import qualified FRP.Parser.Term    as P
import Text.Parsec.String

import FRP.AST
import Text.Parsec
import Language.Haskell.TH.Quote

prog :: QuasiQuoter
prog = QuasiQuoter
  { quoteExp = quoteFRPProg
  , quotePat = undefined -- quoteCmmPat
  , quoteDec = undefined
  , quoteType = undefined
  }

decl :: QuasiQuoter
decl = QuasiQuoter
  { quoteExp = quoteFRPDecl
  , quotePat = undefined -- quoteCmmPat
  , quoteDec = undefined
  , quoteType = undefined
  }

term :: QuasiQuoter
term = QuasiQuoter
  { quoteExp = quoteFRPTerm
  , quotePat = undefined -- quoteCmmPat
  , quoteDec = undefined
  , quoteType = undefined
  }

quoteParseFRP :: Monad m => Parser p -> String -> m p
quoteParseFRP p s = either (fail . show) return $ parse (spaces >> p) "quasi" s

quoteFRPParser p s = do
  ast <- quoteParseFRP p s
  dataToExpQ (const Nothing) ast

quoteFRPDecl = quoteFRPParser P.decl
quoteFRPTerm = quoteFRPParser P.term
quoteFRPProg = quoteFRPParser P.prog



