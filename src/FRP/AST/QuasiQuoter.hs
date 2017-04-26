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
import           Control.Applicative
import           Text.Parsec hiding ((<|>))
import           Data.List (find)
import           Text.Parsec.String
import           Utils (safeLast)

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

progTy :: QuasiQuoter
progTy = QuasiQuoter
  { quoteExp = quoteFRPProgTy
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
  case inferDecl' dcl of
    Left err -> fail . show $ err
    Right ty -> do
          let sing = typeToSingExp (_type dcl)
          let trm = dataToExpQ (const Nothing) (unitFunc $ _body dcl)
          runQ [| FRP initEnv $(trm) $(sing) |]

-- quotes an FRP program
-- the resulting type reflects the type of the definition named "main" or,
-- if there is no such definition, the last definition in the quasiquote
quoteFRPProgTy s = do
  prog <- quoteParseFRP P.prog s
  let decls = _decls prog
  -- stuff related to attempting to implement imports. Didn't work :/
  {- let imports = expsToExp <$> (sequence $ map getImport $ _imports prog)
     let decls' = dataToExpQ (const Nothing) decls :: Q Exp
     let merged = varE (mkName "++") `appE` imports `appE` decls'
     let mergedData = [|$(merged)|] :: [Decl ()]
  -}
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
      -- in  runQ [| FRP $(globals) $(trm) $(sing) |]

expsToExp :: [Exp] -> Exp
expsToExp = foldr (\x acc -> ConE (mkName ":") `AppE` x `AppE` acc)
                          (ConE (mkName "[]"))


getImport :: String -> Q Exp
getImport imp = do
  nm <- lookupValueName imp
  maybe (fail $ "import " ++ imp ++ " not found in scope") varE nm


quoteFRPTerm = quoteFRPParser P.term
quoteFRPProg = quoteFRPParser P.prog



