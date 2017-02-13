module FRP.Parser where

import Text.Parsec
import Text.Parsec.Expr
import Text.Parsec.Language
import Text.Parsec.String
import qualified Text.Parsec.Token as Tok
import Utils

import FRP.AST

opNames    = ["+", "-", "*", "/", "=", "=="
             , "<", ">", "<=", ">=", "\\", "->", "|"
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
                          ]
  , Tok.reservedOpNames = opNames
  , Tok.caseSensitive   = True
  }


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

term = tmlam
   <|> buildExpressionParser table expr
   <?> "term"

expr     =  parens term
        <|> tmcons
        <|> tmpromote
        <|> tmdelay
        <|> tmstable
        <|> tmcase
        <|> tmite
        <|> tmlet
        <|> tmout
        <|> tminto
        <|> try (tminl <|> tminr)
        <|> int
        <|> bool
        <|> var
        <?> "simple expression"

table   = [ [Infix spacef AssocLeft]
          , [binary "*" (bo Mult) AssocLeft, binary "/" (bo Div) AssocLeft ]
          , [binary "+" (bo Add)  AssocLeft, binary "-" (bo Sub) AssocLeft ]
          , [ binary "<" (bo Lt) AssocNone, binary "<=" (bo Leq) AssocNone
            , binary ">" (bo Gt) AssocNone, binary ">=" (bo Geq) AssocNone
            ]
          , [binary "==" (bo Eq) AssocNone]
          ]
          where
            spacef = ws *> notFollowedBy (choice . map reservedOp $ opNames)
                     >> return TmApp
                     <?> "space application"
            bo = TmBinOp

tminl :: Parser Term
tminl = TmInl <$> (reserved "inl" *> term)

tminr :: Parser Term
tminr = TmInr <$> (reserved "inr" *> term)

tmout :: Parser Term
tmout = TmOut <$> (reserved "out" *> term)

tminto :: Parser Term
tminto = TmInto <$> (reserved "into" *> term)

tmcase :: Parser Term
tmcase =
  TmCase <$> (reserved "case" *> term <* reserved "of")
         <*> ((,) <$> (reservedOp "|" *> reserved "inl" *> identifier)
                  <*> (reservedOp "->" *> term))
         <*> ((,) <$> (reservedOp "|" *> reserved "inr" *> identifier)
                  <*> (reservedOp "->" *> term))


tmstable :: Parser Term
tmstable = TmStable <$> (reserved "stable" *> parens term)

tmpromote :: Parser Term
tmpromote = TmPromote <$> (reserved "promote" *> parens term)

tmdelay :: Parser Term
tmdelay = reserved "delay" *> parens (TmDelay <$> term <*> (comma *> term))

tmlam :: Parser Term
tmlam =
  TmLam <$> (symbol "\\" *> identifier)
        <*> (ws *> reservedOp "->" *> term)
  <?> "lambda"

tmite :: Parser Term
tmite =
  TmITE <$> (reserved "if" *> term)
        <*> (reserved "then" *> term)
        <*> (reserved "else" *> term)

tmpattern :: Parser Pattern
tmpattern = PBind  <$> identifier
        <|> PDelay <$> (reserved "delay" *> parens identifier) <* ws
        <|> PStable <$> (reserved "stable" *> parens tmpattern) <* ws
        <|> reserved "cons" *> parens
              (PCons <$> (ws *> tmpattern) <*> (ws *> comma *> tmpattern)) <* ws
        <|> (parens (PTup <$> (ws *> tmpattern) <*> (ws *> comma *> tmpattern))) <* ws

tmlet :: Parser Term
tmlet = TmLet <$> (reserved "let" >> ws >> tmpattern)
              <*> (ws >> reservedOp "=" >> ws >> term)
              <*> (ws >> reserved "in" >> ws >> term)

tmcons :: Parser Term
tmcons = reserved "cons" *> parens
              (TmCons <$> (ws *> term) <*> (comma *> term)) <* ws

var, int, bool :: Parser Term
var  = TmVar <$> identifier
int  = TmLit . LInt . fromInteger <$> integer
bool = TmLit . LBool <$>
  (const True <$> reserved "True" <|> const False <$> reserved "False") <* ws

-- unsafeParse :: String -> Program
-- unsafeParse p = either (error . show) id $ parse term "unsafe" p

parseTerm :: String -> Either ParseError Term
parseTerm p = parse term "FRP" p