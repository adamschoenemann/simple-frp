
module FRP.Parser.Type where

import Text.Parsec
import FRP.AST
import FRP.Parser.Lang
import Text.Parsec.Pos

ty :: Parser (Type SourcePos)
ty =  buildExpressionParser tytable tyexpr
  <?> "type"

withPos :: (SourcePos -> a) -> Parser a
withPos fn = do
  p <- getPosition
  return (fn p)

tytable = [ [ prefix' "S"  (withPos TyStream)
            , prefix' "#" (withPos TyStable)
            , prefix' "@" (withPos TyLater)
            ]
          , [binary' "*"  (withPos TyProd) AssocRight]
          , [binary' "+"  (withPos TySum)  AssocRight]
          , [binary' "->" (withPos TyArr)  AssocRight]
          ]

tyexpr = parens ty
     <|> tynat
     <|> tybool
     <|> tyalloc
     <|> tyvar

tynat = reserved "Nat" >> withPos TyNat
tybool = reserved "Bool" >> withPos TyBool
tyalloc = reserved "alloc" >> withPos TyAlloc
tyvar = withPos TyVar <*> identifier

