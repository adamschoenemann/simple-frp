{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DataKinds #-}

module FRP.AST.QuasiQuoter where

import qualified FRP.Parser.Program as P
import qualified FRP.Parser.Decl    as P
import qualified FRP.Parser.Term    as P

import FRP.AST
import FRP.TypeInference
import FRP.AST.Reflect
import FRP.Pretty

import Text.Parsec.String
import Text.Parsec
import Language.Haskell.TH.Quote
import Language.Haskell.TH

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

declTy :: QuasiQuoter
declTy = QuasiQuoter
  { quoteExp = quoteFRPDeclTy
  , quotePat = undefined
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

quoteFRPDeclTy s = do
  dcl <- quoteParseFRP P.decl s
  _ <- either (fail . ppshow) return (inferDecl' dcl)
  let sing = typeToSingExp (_type dcl)
  let trm = dataToExpQ (const Nothing) (unitFunc $ _body dcl)
  runQ [| FRP $(trm) $(sing)|]



quoteFRPTerm = quoteFRPParser P.term
quoteFRPProg = quoteFRPParser P.prog



