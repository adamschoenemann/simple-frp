{-|
Module      : FRP.AST.QuasiQuoter
Description : Quasi-Quoters for FRP programs
-}
{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NamedFieldPuns            #-}
{-# LANGUAGE BangPatterns #-}

module FRP.AST.QuasiQuoter where

import qualified FRP.Parser.Decl           as P
import qualified FRP.Parser.Program        as P
import qualified FRP.Parser.Term           as P

import           FRP.AST hiding (Name)
import           FRP.AST.Reflect
import           FRP.Pretty
import           FRP.TypeInference
import           FRP.Semantics
import           Utils (safeLast)

import           Language.Haskell.TH
import           Language.Haskell.TH.Quote
import           Data.Maybe (catMaybes)
import           Data.Data
import           Control.Applicative
import           Text.Parsec hiding ((<|>))
import           Data.List (find)
import           Text.Parsec.String
import           Control.Monad.Fix
import           Debug.Trace

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
  , quotePat = undefined  -- we don't use it in pattern positions
  , quoteDec = undefined  -- we don't use it in declaration positions
  , quoteType = undefined -- we don't use it in type positions
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

hsterm :: QuasiQuoter
hsterm = QuasiQuoter
  { quoteExp = quoteHsTerm
  , quotePat = undefined
  , quoteDec = undefined
  , quoteType = undefined
  }

hsprog :: QuasiQuoter
hsprog = QuasiQuoter
  { quoteExp = undefined
  , quotePat = undefined
  , quoteDec = quoteHsProg
  , quoteType = undefined
  }

quoteHsTerm s = do
  ast <- parseFRP P.term s
  exp <- termToHaskExpQ ast
  return exp

quoteHsProg :: String -> Q [Dec]
quoteHsProg s = do
  ast <- parseFRP P.prog s
  -- imports are impossibruh! :/
  -- runIO $ print $ _imports ast
  -- ms <- mapM (lookupValueName . (++ "_type")) $ _imports ast
  -- let infos = catMaybes ms
  -- infos <- lookupValueName "tail"
  -- runIO $ print infos
  case inferProg emptyCtx ast of
    Left err -> fail (ppshow err ++ "\ninput:\n" ++ s)
    Right ty -> progToHaskDecls ast

-- importsToCtx :: [String] -> Ctx SourcePos
-- importsToCtx

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
      sing <- typeToSingExp (_type dcl)
      trm  <- dataToExpQ (const Nothing) (unitFunc $ _body dcl)
      env  <- dataToExpQ (const Nothing) initEnv
      return $ ConE 'FRP `AppE` env `AppE` trm `AppE` sing
          -- runQ [| FRP initEnv $(trm) $(sing) |]

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
      return (ConE 'FRP `AppE` globals `AppE` trm `AppE` sing)

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


newtype Mu f = Into { out :: f (Mu f) }

progToHaskDecls :: Data a => Program a -> Q [Dec]
progToHaskDecls (Program { _decls = decls }) = do
  sequence . concat . map declToHaskDec $ decls where
    declToHaskDec :: Data a => Decl a -> [DecQ]
    declToHaskDec (Decl {_name, _type, _body}) =
      [ valD (varP (mkName _name)) (normalB $ termToHaskExpQ _body) []
      , valD (varP (mkName $ _name ++ "_type"))
          (normalB $ dataToExpQ (const Nothing) _type) []
      ]

delay :: () -> a -> a
delay !u a = a

termToHaskExpQ :: Term a -> ExpQ
termToHaskExpQ term = go term where
  go = \case
    TmFst a t                    -> [|fst $(go t)|]
    TmSnd a t                    -> [|snd $(go t)|]
    TmTup a t1 t2                -> [|($(go t1), $(go t2))|]
    TmInl a t                    -> [|Left  $(go t)|]
    TmInr a t                    -> [|Right $(go t)|]
    TmCase a t (ln, lt) (rn, rt) ->
        [| case $(go t) of
             Left  $(varP (mkName ln)) -> $(go lt)
             Right $(varP (mkName rn)) -> $(go rt)
        |]
    TmLam a nm mty t             -> lamE [bangP . varP $ mkName nm] (go t)
    TmVar a nm                   -> varE (mkName nm)
    TmApp a  t1 t2               -> [|$(go t1) $(go t2)|]
    TmCons a t1 t2               -> conE (mkName ":") `appE` go t1 `appE` go t2 -- [|$(go t1) : $(go t2)|]
    TmOut a  _ t                 -> [|out $(go t)|]
    TmInto a _ t                 -> [|Into $(go t)|]
    TmStable a t                 -> go t
    TmDelay a t1 t2              -> go t2 -- varE 'delay `appE` go t1 `appE` go t2
    TmPromote a t                -> go t
    TmLet a pat t1 t2            -> letE [patToHaskDecQ pat t1] (go t2)
    TmLit a l                    -> case l of
      LNat x                     -> litE (integerL (toInteger x))
      LBool True                 -> conE 'True
      LBool False                -> conE 'False
      LUnit                      -> conE '()
      LUndefined                 -> varE (mkName "undefined")
    TmBinOp a op t1 t2           -> [| $(varE $ mkName (ppshow op)) $(go t1) $(go t2) |]
    TmITE a b tt tf              -> [|if $(go b) then $(go tt) else $(go tf)|]
    TmPntr a lbl                 -> undefined
    TmPntrDeref a lbl            -> undefined
    TmInput a nm                 -> undefined
    TmAlloc a                    -> conE '()
    TmFix a nm mty t             -> (varE 'fix) `appE` (lamE [varP $ mkName nm] (go t))

patToHaskDecQ :: Pattern -> Term a -> DecQ
patToHaskDecQ pat term = valD (go $ pat) (normalB $ termToHaskExpQ term) []
  where
    go pat = case pat of
        PBind nm  -> varP $ mkName nm
        PDelay nm -> varP $ mkName nm
        PTup p1 p2 -> tupP [go p1, go p2]
        PCons p1 p2 -> conP (mkName ":") [go p1, go p2]
        PStable p   -> go p




