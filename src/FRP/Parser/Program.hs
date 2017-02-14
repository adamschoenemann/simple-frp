
module FRP.Parser.Program where

import Text.Parsec
import FRP.AST (Program(..), _name)
import FRP.Parser.Lang
import FRP.Parser.Decl
import Text.Parsec.Char (endOfLine)
import Data.List (find)

prog :: Parser Program
prog = do
  decls <- many decl
  -- let mainM = Just $ head decls
  let mainM = find (\d -> _name d == "main") decls
  let notMain = filter (\d -> _name d /= "main") decls
  maybe (fail "No main function") (\mn -> return $ Program mn notMain) mainM