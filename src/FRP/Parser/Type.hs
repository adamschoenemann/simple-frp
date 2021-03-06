
module FRP.Parser.Type where

import Text.Parsec
import FRP.AST
import FRP.Parser.Lang
import Text.Parsec.Pos

ty :: Parser (Type SourcePos)
ty =  tyrec <|> buildExpressionParser tytable tyexpr
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

tyexpr = tyunit
     <|> tynat
     <|> tybool
     <|> tyalloc
     <|> tyvar
     <|> parens ty

tyunit  = reserved "()" >> withPos (flip TyPrim $ TyUnit)
tynat   = reserved "Nat"   >> withPos (\p -> TyPrim p TyNat)
tybool  = reserved "Bool" >> withPos (\p -> TyPrim p TyBool)
tyalloc = reserved "alloc" >> withPos TyAlloc
tyvar = withPos TyVar <*> identifier

tyrec = withPos TyRec <*> (reserved "mu" *> identifier <* symbol ".") <*> ty
-- tyrec = do
--   _ <- reserved "mu"
--   v <- identifier
--   _ <- symbol "."
--   withPos TyRec <*> return v <*> ty


