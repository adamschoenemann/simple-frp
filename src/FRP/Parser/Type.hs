
module FRP.Parser.Type where

import Text.Parsec
import FRP.AST
import FRP.Parser.Lang

ty :: Parser Type
ty =  buildExpressionParser tytable tyexpr
  <?> "type"

tytable = [ [prefix "S"  TyStream, prefix "#" TyStable, prefix "@" TyLater]
          , [binary "*"  TyProd AssocRight]
          , [binary "+"  TySum  AssocRight]
          , [binary "->" TyArr  AssocRight]
          ]

tyexpr = parens ty
     <|> tynat
     -- <|> tybool
     <|> tyalloc
     <|> typaram

tynat = reserved "Nat" >> return TyNat
tyalloc = reserved "alloc" >> return TyAlloc
typaram = TyParam <$> identifier

