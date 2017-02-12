module FRP.Parser where

import Text.Parsec
import Text.Parsec.Expr
import Text.Parsec.Language
import Text.Parsec.String
import qualified Text.Parsec.Token as Tok
import Utils

import FRP.AST

opNames    = ["+", "-", "*", "/", ":="
             , "<", ">", "<=", ">=", "\\", "->"
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
                          ]
  , Tok.reservedOpNames = opNames
  , Tok.caseSensitive   = True
  }

expr    = buildExpressionParser table term
         <?> "expression"

term     =  parens expr
        <|> tmlet
        <|> tmcons
        -- <|> tmlam
        <|> TmLit . LInt . fromInteger <$> integer
        <|> TmVar <$> identifier
        <?> "simple expression"

table   = [ [Infix spacef AssocLeft]
          , [binary "*" (bo Mult) AssocLeft, binary "/" (bo Div) AssocLeft ]
          , [binary "+" (bo Add)  AssocLeft, binary "-" (bo Sub) AssocLeft ]
          , [Prefix (reservedOp "\\" >> ws >> TmLam <$> identifier <* ws <* reservedOp "->" <* ws)]
          ]
          where

            bo = TmBinOp


spacef = ws
         *> notFollowedBy (choice . map reservedOp $ opNames)
         >> return TmApp
         <?> "space application"

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

tmlam :: Parser Term
tmlam =
  TmLam <$> (char '\\' *> ws *> identifier)
        <*> (ws *> string "->" *> ws *> term)
  <?> "lambda"

tmpattern :: Parser Pattern
tmpattern = PBind  <$> (identifier) <* ws
        <|> PDelay <$> (string "delay" *> parens identifier) <* ws
        <|> PStable <$> (string "stable" *> parens tmpattern) <* ws
        <|> string "cons" *> ws *> parens (PCons <$> (ws *> tmpattern) <*> (ws *> char ',' *> tmpattern)) <* ws
        <|> (parens (PTup <$> (ws *> tmpattern) <*> (ws *> char ',' *> ws *> tmpattern))) <* ws

tmlet :: Parser Term
tmlet = TmLet <$> (string "let" >> ws >> tmpattern)
              <*> (ws >> char '=' >> ws >> term)
              <*> (ws >> string "in" >> ws >> term)

tmcons :: Parser Term
tmcons = string "cons" *> ws *> parens (TmCons <$> (ws *> term) <*> (char ',' *> ws *> term)) <* ws

tmapp :: Parser Term
tmapp = var `chainl1` (const TmApp <$> many1 space) <* ws

-- term :: Parser Term
-- term = ws *> prs where
--   prs = tmlet
--     <|> tmlam
--     <|> tmcons
--     <|> tmexpr
--     <|> parens term

tmexpr :: Parser Term
tmexpr = equality
  where
    equality   = comparison `chainl1` cmpop
    comparison = intexpr    `chainl1` intop
    intexpr    = term       `chainl1` termop
    term       = factor     `chainl1` factop
    factor     = prim       --`chainl1` appop
    prim       = ((parens term) <|> try tmapp <|> int <|> bool <|> var) <* ws
    cmpop  =  const (TmBinOp Eq)   <$> string "==" <* ws
    intop  =  const (TmBinOp Gt)   <$> char   '>'  <* ws
          <|> const (TmBinOp Lt)   <$> char   '<'  <* ws
    termop =  const (TmBinOp Add)  <$> char   '+'  <* ws
          <|> const (TmBinOp Sub)  <$> char   '-'  <* ws
    factop =  const (TmBinOp Mult) <$> char   '*'  <* ws

var, int, bool :: Parser Term
var  = TmVar <$> ident
int  = TmLit . LInt  . read <$> many1 digit <* ws
bool = TmLit . LBool . read . capitalize <$> (string "true" <|> string "false") <* ws

-- parens, brackets :: Parser a -> Parser a
-- parens x = between (char '(' <* spaces) (char ')') (x <* spaces)
-- brackets x = between (char '{' <* spaces) (char '}') (x <* spaces)

ident :: Parser String
ident  = (\l a c -> l : a ++ c) <$> letter <*> many alphaNum <*> many (char '\'')

-- unsafeParse :: String -> Program
-- unsafeParse p = either (error . show) id $ parse program "unsafe" p

parseTerm :: String -> Either ParseError Term
parseTerm p = parse expr "FRP" p