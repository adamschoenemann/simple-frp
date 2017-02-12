module FRP.Parser where

import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token
import Utils

import FRP.AST


languageDef =
  emptyDef { Token.commentStart    = "{-"
           , Token.commentEnd      = "-}"
           , Token.commentLine     = "--"
           , Token.identStart      = letter
           , Token.identLetter     = alphaNum
           , Token.reservedNames   = [ "if"
                                     , "then"
                                     , "else"
                                     , "True"
                                     , "False"
                                     ]
           , Token.reservedOpNames = ["+", "-", "*", "/", "="
                                     , "<", ">", "&&", "||", "not"
                                     , "<=", ">="
                                     ]
           }


lexer = Token.makeTokenParser languageDef
identifier = Token.identifier lexer -- parses an identifier
reserved   = Token.reserved   lexer -- parses a reserved name
reservedOp = Token.reservedOp lexer -- parses an operator
parens     = Token.parens     lexer -- parses surrounding parenthesis:
                                    --   parens p
                                    -- takes care of the parenthesis and
                                    -- uses p to parse what's inside them
integer    = Token.integer    lexer -- parses an integer
semi       = Token.semi       lexer -- parses a semicolon
ws = Token.whiteSpace lexer -- parses whitespace

tmlam :: Parser Term
tmlam =
  TmLam <$> (ws *> char '\\' *> ws *> identifier)
        <*> (ws *> string "->" *> term)

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
tmapp = var `chainl1` (const TmApp <$> many1 space)

term :: Parser Term
term = ws *> prs where
  prs = tmlet
    <|> tmlam
    <|> tmcons
    <|> tmexpr
    <|> parens term

tmexpr :: Parser Term
tmexpr = equality
  where
    equality   = comparison `chainl1` cmpop
    comparison = intexpr    `chainl1` intop
    intexpr    = term       `chainl1` termop
    term       = factor     `chainl1` factop
    factor     = prim       `chainl1` appop
    prim       = ((parens term) <|> int <|> bool <|> var) <* ws
    appop  =  const  TmApp         <$> many1 space
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
parseTerm p = parse term "FRP" p