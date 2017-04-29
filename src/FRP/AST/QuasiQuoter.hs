{-|
Module      : FRP.AST.QuasiQuoter
Description : Quasi-Quoters for FRP programs
-}
{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE TemplateHaskell #-}

module FRP.AST.QuasiQuoter where

import qualified FRP.Parser.Decl           as P
import qualified FRP.Parser.Program        as P
import qualified FRP.Parser.Term           as P

import           FRP.AST hiding (Name)
import           FRP.AST.Reflect
import           FRP.Pretty
import           FRP.TypeInference
import           FRP.Semantics

import           Language.Haskell.TH
import           Language.Haskell.TH.Quote
import           Data.Data
import           Control.Applicative
import           Text.Parsec hiding ((<|>))
import           Data.List (find)
import           Text.Parsec.String
import           Utils (safeLast)

-- |Quote a program without type-checking it
unsafeProg :: QuasiQuoter
unsafeProg = QuasiQuoter
  { quoteExp = unsafeQuoteProg
  , quotePat = undefined
  , quoteDec = undefined
  , quoteType = undefined
  }

-- |Quote a declaration without type-checking it
unsafeDecl :: QuasiQuoter
unsafeDecl = QuasiQuoter
  { quoteExp = unsafeQuoteDecl
  , quotePat = undefined
  , quoteDec = undefined
  , quoteType = undefined
  }

-- |Quote and type-check a declaration
decl :: QuasiQuoter
decl = QuasiQuoter
  { quoteExp = quoteFRPDecl
  , quotePat = undefined
  , quoteDec = undefined
  , quoteType = undefined
  }

-- |Quote and type-check a program
prog :: QuasiQuoter
prog = QuasiQuoter
  { quoteExp = quoteProg
  , quotePat = undefined
  , quoteDec = undefined
  , quoteType = undefined
  }

-- |Quote a term without type-checking it
unsafeTerm :: QuasiQuoter
unsafeTerm = QuasiQuoter
  { quoteExp = unsafeQuoteTerm
  , quotePat = undefined
  , quoteDec = undefined
  , quoteType = undefined
  }

-- |Helper function for quoting the result of a parser
parseFRP :: Monad m => Parser p -> String -> m p
parseFRP p s = either (fail . show) return $ parse (spaces >> p) "quasi" s

-- |Unsafely quote the result of a parser
unsafeQuoteFRPParser :: Data a => Parser a -> String -> Q Exp
unsafeQuoteFRPParser p s = do
  ast <- parseFRP p s
  dataToExpQ (const Nothing) ast

unsafeQuoteDecl, unsafeQuoteTerm, unsafeQuoteProg :: String -> Q Exp
unsafeQuoteDecl = unsafeQuoteFRPParser P.decl
unsafeQuoteTerm = unsafeQuoteFRPParser P.term
unsafeQuoteProg = unsafeQuoteFRPParser P.prog

-- |Quote and type-check a declaration
quoteFRPDecl :: String -> Q Exp
quoteFRPDecl s = do
  dcl <- parseFRP P.decl s
  case inferDecl' dcl of
    Left err -> fail . show $ err
    Right ty -> do
          let sing = typeToSingExp (_type dcl)
          let trm = dataToExpQ (const Nothing) (unitFunc $ _body dcl)
          runQ [| FRP initEnv $(trm) $(sing) |]

-- |Quotes an FRP program.
-- The resulting type reflects the type of the definition named "main" or,
-- if there is no such definition, the last definition in the quasiquote.
quoteProg :: String -> Q Exp
quoteProg s = do
  prog <- parseFRP P.prog s
  let decls = _decls prog
  mainDecl <-
        maybe (fail "empty programs are not allowed") return $
          find (\d -> _name d == "main") decls <|> safeLast decls
  case inferProg emptyCtx prog of
    Left err -> fail . show $ err
    Right (Ctx ctx) -> do
      let ty      = _type mainDecl
      sing    <- typeToSingExp ty
      trm     <- dataToExpQ (const Nothing) (unitFunc $ _body mainDecl)
      globals <- dataToExpQ (const Nothing) (globalEnv decls)
      return (ConE (mkName "FRP") `AppE` globals `AppE` trm `AppE` sing)

-- stuff related to attempting to implement imports. Didn't work :/
{- let imports = expsToExp <$> (sequence $ map getImport $ _imports prog)
   let decls' = dataToExpQ (const Nothing) decls :: Q Exp
   let merged = varE (mkName "++") `appE` imports `appE` decls'
   let mergedData = [|$(merged)|] :: [Decl ()]

expsToExp :: [Exp] -> Exp
expsToExp = foldr (\x acc -> ConE (mkName ":") `AppE` x `AppE` acc)
                          (ConE (mkName "[]"))
getImport :: String -> Q Exp
getImport imp = do
  nm <- lookupValueName imp
  maybe (fail $ "import " ++ imp ++ " not found in scope") varE nm
-}






