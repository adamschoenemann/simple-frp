
module FRP.Parser.Decl where

import Text.Parsec
import FRP.AST
import FRP.Parser.Lang
import FRP.Parser.Term
import FRP.Parser.Type
import Text.Parsec.Char (endOfLine)

decl :: Parser Decl
decl = do
  nam <- identifier
  typ <- reservedOp ":" *> ty
  _   <- string nam <* ws
  params <- many identifier <* ws <* reservedOp "="
  bod <- term <* char '.' <* ws
  let body = paramsToLams params bod
  return $ Decl typ nam body

