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
  TmLam <$> (ws >> string "fun" >> ws >> identifier)
        <*> (ws >> string "->" >> term)


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

term :: Parser Term
term = ws *> prs where
  prs = tmlet
    <|> tmlam
    <|> tmcons
    <|> tmexpr

-- program :: Parser Program
-- program = spaces *> many (stmt <* spaces)

-- stmt :: Parser SubProg
-- stmt =  (const $ Single Skip) <$> trystring "skip" <* spaces <* char ';' <* spaces
--     <|> ITE <$> (trystring "if" *> spaces1 *> expr) <*>
--                 (trystring "then" *> spaces1 *> stmt <* spaces) <*>
--                 (trystring "else" *> spaces1 *> stmt <* spaces)
--     <|> While <$> (trystring "while" *> spaces1 *> expr) <*>
--                   (trystring "do" *> spaces1 *> stmt) <* spaces
--     <|> (Single . Output) <$> (trystring "output" *> spaces1 *> expr <* char ';') <* spaces
--     <|> (\v e -> Single $ Ass v e) <$> (ident <* spaces)
--                                    <*> (string ":=" *> spaces *> expr <* char ';') <* spaces
--     <|> Block <$> (brackets block) <* spaces
--       where
--         block = sepBy stmt spaces

-- trystring :: String -> Parser String
-- trystring = try . string

-- spaces1 :: Parser String
-- spaces1 = many1 space

tmexpr :: Parser Term
tmexpr = equality
  where
    equality   = comparison `chainl1` cmpop
    comparison = intexpr    `chainl1` intop
    intexpr    = term       `chainl1` termop
    term       = factor     `chainl1` factop
    factor     = (parens tmexpr) <* spaces <|> int <|> bool <|> var
    cmpop  =  const (TmBinOp Eq)   <$> string "==" <* spaces
    intop  =  const (TmBinOp Gt)   <$> char   '>'  <* spaces
          <|> const (TmBinOp Lt)   <$> char   '<'  <* spaces
    termop =  const (TmBinOp Add)  <$> char   '+'  <* spaces
          <|> const (TmBinOp Sub)  <$> char   '-'  <* spaces
    factop =  const (TmBinOp Mult) <$> char   '*'  <* spaces

-- var, int, bool :: Parser Expr
var  = TmVar <$> identifier <* ws
int  = TmLit . LInt  . read <$> many1 digit <* ws
bool = TmLit . LBool . read . capitalize <$> (string "true" <|> string "false") <* ws

-- parens, brackets :: Parser a -> Parser a
-- parens x = between (char '(' <* spaces) (char ')') (x <* spaces)
-- brackets x = between (char '{' <* spaces) (char '}') (x <* spaces)

-- ident :: Parser String
-- ident  = (:) <$> letter <*> many alphaNum

-- unsafeParse :: String -> Program
-- unsafeParse p = either (error . show) id $ parse program "unsafe" p

parseTerm :: String -> Either ParseError Term
parseTerm p = parse tmexpr "FRP" p