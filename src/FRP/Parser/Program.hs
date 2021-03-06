
module FRP.Parser.Program where

import Text.Parsec
import FRP.AST (Program(..), _name)
import FRP.Parser.Lang
import FRP.Parser.Decl
import Text.Parsec.Char (endOfLine)
import Data.List (find)

prog :: Parser (Program SourcePos)
prog = do
  imports <- many importp
  decls <- many decl
  _ <- eof
  return $ Program imports decls

importp = reserved "import" >> identifier <* symbol "."