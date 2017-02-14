
module FRP.Parser.Decl where

import Text.Parsec
import FRP.AST
import FRP.Parser.Lang
import FRP.Parser.Term
import FRP.Parser.Type
import Text.Parsec.Char (endOfLine)

-- eol = (try (string "\r\n")) <|> string "\n"

decl :: Parser Decl
decl = do
  nam <- identifier
  typ <- reservedOp ":" *> ty
  _   <- string nam <* ws <* reservedOp "="
  bod <- term
  return $ Decl typ nam bod