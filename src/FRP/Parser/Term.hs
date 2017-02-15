module FRP.Parser.Term where

import Text.Parsec
import FRP.AST
import qualified FRP.AST.Construct as C
import FRP.Parser.Lang

type ParsedTerm = Term ()

term = tmlam
   <|> buildExpressionParser tmtable tmexpr
   <?> "term"

tmexpr = tmcons
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

tmtable   = [ [Infix spacef AssocLeft]
          , [binary "*" (bo Mult) AssocLeft, binary "/" (bo Div) AssocLeft ]
          , [binary "+" (bo Add)  AssocLeft, binary "-" (bo Sub) AssocLeft ]
          , [ binary "<" (bo Lt) AssocNone, binary "<=" (bo Leq) AssocNone
            , binary ">" (bo Gt) AssocNone, binary ">=" (bo Geq) AssocNone
            ]
          , [binary "==" (bo Eq) AssocNone]
          ]
          where
            spacef = ws *> notFollowedBy (choice . map reservedOp $ opNames)
                     >> return C.tmapp
                     <?> "space application"
            bo = C.tmbinop

tmtup :: Parser ParsedTerm
tmtup = parens (C.tmtup <$> (term <* comma) <*> term)

tmsnd :: Parser ParsedTerm
tmsnd = C.tmsnd <$> (reserved "snd" *> tmexpr)

tmfst :: Parser ParsedTerm
tmfst = C.tmfst <$> (reserved "fst" *> tmexpr)

tminl :: Parser ParsedTerm
tminl = C.tminl <$> (reserved "inl" *> tmexpr)

tminr :: Parser ParsedTerm
tminr = C.tminr <$> (reserved "inr" *> tmexpr)

tmout :: Parser ParsedTerm
tmout = C.tmout <$> (reserved "out" *> tmexpr)

tminto :: Parser ParsedTerm
tminto = C.tminto <$> (reserved "into" *> tmexpr)

tmcase :: Parser ParsedTerm
tmcase =
  C.tmcase <$> (reserved "case" *> term <* reserved "of")
         <*> ((,) <$> (reservedOp "|" *> reserved "inl" *> identifier)
                  <*> (reservedOp "->" *> term))
         <*> ((,) <$> (reservedOp "|" *> reserved "inr" *> identifier)
                  <*> (reservedOp "->" *> term))


tmstable :: Parser ParsedTerm
tmstable = C.tmstable <$> (reserved "stable" *> parens term)

tmpromote :: Parser ParsedTerm
tmpromote = C.tmpromote <$> (reserved "promote" *> parens term)

tmdelay :: Parser ParsedTerm
tmdelay = reserved "delay" *> parens (C.tmdelay <$> term <*> (comma *> term))

tmlam :: Parser ParsedTerm
tmlam = do
  params <- symbol "\\" *> many1 identifier
  bd <- reservedOp "->" *> term
  let lams = paramsToLams params
  return (lams bd)

tmite :: Parser ParsedTerm
tmite =
  C.tmite <$> (reserved "if" *> term)
          <*> (reserved "then" *> term)
          <*> (reserved "else" *> term)

tmpattern :: Parser Pattern
tmpattern = PBind  <$> identifier
        <|> PDelay <$> (reserved "delay" *> parens identifier) <* ws
        <|> PStable <$> (reserved "stable" *> parens tmpattern) <* ws
        <|> reserved "cons" *> parens
              (PCons <$> (ws *> tmpattern) <*> (ws *> comma *> tmpattern)) <* ws
        <|> (parens (PTup <$> (ws *> tmpattern) <*> (ws *> comma *> tmpattern))) <* ws

tmlet :: Parser ParsedTerm
tmlet = C.tmlet <$> (reserved "let" >> ws >> tmpattern)
              <*> (ws >> reservedOp "=" >> ws >> term)
              <*> (ws >> reserved "in" >> ws >> term)

tmcons :: Parser ParsedTerm
tmcons = reserved "cons" *> parens
              (C.tmcons <$> (ws *> term) <*> (comma *> term)) <* ws

var, int, bool :: Parser ParsedTerm
var  = C.tmvar <$> identifier
int  = C.tmlit . LInt . fromInteger <$> integer
bool = C.tmlit . LBool <$>
  (const True <$> reserved "True" <|> const False <$> reserved "False") <* ws


parseParsedTerm :: String -> Either ParseError ParsedTerm
parseParsedTerm p = parse term "FRP" p