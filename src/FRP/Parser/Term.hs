module FRP.Parser.Term where

import Text.Parsec
import FRP.AST
import FRP.Parser.Lang

term = tmlam
   <|> buildExpressionParser table expr
   <?> "term"

expr  =  tmcons
     <|> tmpromote
     <|> tmdelay
     <|> tmstable
     <|> tmcase
     <|> tmite
     <|> tmlet
     <|> tmout
     <|> tminto
     <|> tminl
     <|> tminr
     <|> tmfst
     <|> tmsnd
     <|> int
     <|> bool
     <|> var
     <|> try tmtup
     <|> parens term
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

tmtup :: Parser Term
tmtup = parens (TmTup <$> (term <* comma) <*> term)

tmsnd :: Parser Term
tmsnd = TmSnd <$> (reserved "snd" *> expr)

tmfst :: Parser Term
tmfst = TmFst <$> (reserved "fst" *> expr)

tminl :: Parser Term
tminl = TmInl <$> (reserved "inl" *> expr)

tminr :: Parser Term
tminr = TmInr <$> (reserved "inr" *> expr)

tmout :: Parser Term
tmout = TmOut <$> (reserved "out" *> expr)

tminto :: Parser Term
tminto = TmInto <$> (reserved "into" *> expr)

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
tmlam = do
  params <- symbol "\\" *> many1 identifier
  bd <- reservedOp "->" *> term
  let lams = paramsToLams params
  return (lams bd)

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

unsafeParse :: Parser Program -> String -> Program
unsafeParse p s = either (error . show) id $ parse p "unsafe" s

parseTerm :: String -> Either ParseError Term
parseTerm p = parse term "FRP" p