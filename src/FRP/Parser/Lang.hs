
module FRP.Parser.Lang (
    module FRP.Parser.Lang
  , Operator(..)
  , Assoc(..)
  , Parser
  , buildExpressionParser
) where

import Text.Parsec.String
import Text.Parsec
import Text.Parsec.Expr
import qualified Text.Parsec.Token as Tok

-- (<$$>) :: (Functor f, Monad f) => (a -> f b) -> f a -> f b
-- (<$$>) fn x = x >>= fn


opNames :: [String]
opNames    = [ "+", "-", "*", "/", "=", "==", "&&", "||"
             , "<", ">", "<=", ">=", "\\", "->", "|", ":", "."
             ]

languageDef :: Tok.LanguageDef ()
languageDef = Tok.LanguageDef
  { Tok.commentStart    = "{-"
  , Tok.commentEnd      = "-}"
  , Tok.commentLine     = "--"
  , Tok.nestedComments  = True
  , Tok.identStart      = letter
  , Tok.identLetter     = alphaNum <|> oneOf "_'"
  , Tok.opStart         = oneOf ":!#$%&*+./<=>?@\\^|-~"
  , Tok.opLetter        = oneOf ":!#$%&*+./<=>?@\\^|-~"
  , Tok.reservedNames   = [ "if"
                          , "then"
                          , "else"
                          , "True"
                          , "False"
                          , "cons"
                          , "let"
                          , "in"
                          , "delay"
                          , "stable"
                          , "promote"
                          , "fst"
                          , "snd"
                          , "promote"
                          , "inl"
                          , "inr"
                          , "case"
                          , "of"
                          , "out"
                          , "into"
                          , "Nat"
                          , "Bool"
                          , "S"
                          , "alloc"
                          , "fix"
                          ]
  , Tok.reservedOpNames = opNames
  , Tok.caseSensitive   = True
  }

binary'  name fun assoc = Infix   (reservedOp name >> fun) assoc
prefix'  name fun       = Prefix  (reservedOp name >> fun)
postfix' name fun       = Postfix (reservedOp name >> fun)

binary  name fun assoc = Infix   (reservedOp name >> return fun) assoc
prefix  name fun       = Prefix  (reservedOp name >> return fun)
postfix name fun       = Postfix (reservedOp name >> return fun)

lexer      = Tok.makeTokenParser languageDef
identifier = Tok.identifier lexer -- parses an identifier
reserved   = Tok.reserved   lexer -- parses a reserved name
reservedOp = Tok.reservedOp lexer -- parses an operator
parens     = Tok.parens     lexer -- parses surrounding parenthesis:
                                    --   parens p
                                    -- takes care of the parenthesis and
                                    -- uses p to parse what's inside them
integer    = Tok.integer    lexer -- parses an integer
natural    = Tok.natural    lexer
ws         = Tok.whiteSpace lexer -- parses whitespace
comma      = Tok.comma lexer
symbol     = Tok.symbol lexer
