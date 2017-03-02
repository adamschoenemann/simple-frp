
module FRP.Parser.Decl where

import Text.Parsec
import FRP.AST
import FRP.Parser.Lang
import FRP.Parser.Term
import FRP.Parser.Type
import Text.Parsec.Char (endOfLine)

decl :: Parser (Decl SourcePos)
decl = do
  nam <- identifier
  typ <- reservedOp ":" *> ty
  _   <- string nam <* ws
  params <- map (\x -> (x, Nothing)) <$> many identifier <* ws <* reservedOp "="
  bod <- term <* char '.' <* ws
  p <- getPosition
  let body = paramsToLams' p params bod
  return $ Decl p typ nam body

