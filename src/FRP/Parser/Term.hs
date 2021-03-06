module FRP.Parser.Term (
    module FRP.Parser.Term
  , ParsedTerm
) where

import           FRP.AST
import           FRP.Parser.Construct (ParsedTerm)
import qualified FRP.Parser.Construct as C
import           FRP.Parser.Lang
import           FRP.Parser.Type
import           Text.Parsec
import           Text.Parsec.Pos

test :: Parser (Term SourcePos)
test = (TmVar <$> getPosition) <*> identifier
  -- p <- getPosition
  -- return (TmVar p)

term = tmlam
   <|> tmfix
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
     <|> undef
     <|> try tmtup
     <|> unit
     <|> parens term
     <?> "simple expression"

tmtable   = [ [Infix spacef AssocLeft]
            , [prefix "-" (negation)]
            , [binary' "*" (bo Mult) AssocLeft, binary' "/" (bo Div) AssocLeft ]
            , [binary' "+" (bo Add)  AssocLeft, binary' "-" (bo Sub) AssocLeft ]
            , [ binary' "<" (bo Lt) AssocNone, binary' "<=" (bo Leq) AssocNone
              , binary' ">" (bo Gt) AssocNone, binary' ">=" (bo Geq) AssocNone
              ]
            , [binary' "||" (bo Or) AssocLeft]
            , [binary' "&&" (bo And) AssocLeft]
            , [binary' "==" (bo Eq) AssocNone]
            ]
          where
            spacef = ws *> notFollowedBy (choice . map reservedOp $ opNames)
                     >> C.tmapp
                     <?> "space application"
            negation p =
              let TmLit pos (LNat x) = p
              in TmLit pos (LNat (negate x))

            negation' = C.tmbinop <*> return Sub <*> one
            one = do
              pos <- getPosition
              return $ TmLit pos (LNat 1)
            bo o = C.tmbinop <*> return o

tmtup :: Parser ParsedTerm
tmtup = parens (C.tmtup <*> (term <* comma) <*> term)

tmsnd :: Parser ParsedTerm
tmsnd = C.tmsnd <*> (reserved "snd" *> tmexpr)

tmfst :: Parser ParsedTerm
tmfst = C.tmfst <*> (reserved "fst" *> tmexpr)

tminl :: Parser ParsedTerm
tminl = C.tminl <*> (reserved "inl" *> tmexpr)

tminr :: Parser ParsedTerm
tminr = C.tminr <*> (reserved "inr" *> tmexpr)

tmout :: Parser ParsedTerm
tmout = do
  _ <- reserved "out"
  ty <- parens ty
  expr <- tmexpr
  C.tmout <*> return ty <*> return expr

tminto :: Parser ParsedTerm
tminto = do
  _ <- reserved "into"
  ty <- parens ty
  expr <- tmexpr
  C.tminto <*> return ty <*> return expr

tmcase :: Parser ParsedTerm
tmcase =
  C.tmcase <*> (reserved "case" *> term <* reserved "of")
         <*> ((,) <$> (reservedOp "|" *> reserved "inl" *> identifier)
                  <*> (reservedOp "->" *> term))
         <*> ((,) <$> (reservedOp "|" *> reserved "inr" *> identifier)
                  <*> (reservedOp "->" *> term))


tmstable :: Parser ParsedTerm
tmstable = C.tmstable <*> (reserved "stable" *> parens term)

tmpromote :: Parser ParsedTerm
tmpromote = C.tmpromote <*> (reserved "promote" *> parens term)

tmdelay :: Parser ParsedTerm
tmdelay = reserved "delay" *> parens (C.tmdelay <*> term <*> (comma *> term))

tmlam :: Parser ParsedTerm
tmlam = do
  params <- symbol "\\" *> many1 lamParam
  bd <- reservedOp "->" *> term
  p <- getPosition
  let lams = paramsToLams p params
  return (lams bd)
  where
    lamParam = (\x -> (x,Nothing)) <$> identifier
           <|> parens ((,) <$> identifier <*> (optionMaybe (reservedOp ":" *> ty)))

tmparam = (\x -> (x,Nothing)) <$> identifier
           <|> parens ((,) <$> identifier <*> (optionMaybe (reservedOp ":" *> ty)))

tmfix :: Parser ParsedTerm
tmfix = do
  _ <- reserved "fix"
  (nm, ty) <- tmparam
  trm <- reservedOp "." *> term
  C.tmfix <*> return nm <*> return ty <*> return trm


tmite :: Parser ParsedTerm
tmite =
  C.tmite <*> (reserved "if" *> term)
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
tmlet = C.tmlet <*> (reserved "let" >> ws >> tmpattern)
              <*> (ws >> reservedOp "=" >> ws >> term)
              <*> (ws >> reserved "in" >> ws >> term)

tmcons :: Parser ParsedTerm
tmcons = reserved "cons" *> parens
              (C.tmcons <*> (ws *> term) <*> (comma *> term)) <* ws

var, unit, int, bool, undef :: Parser ParsedTerm
var  = C.tmvar <*> identifier
unit = reserved "()" >> C.tmlit <*> return LUnit
undef  = reserved "undefined" >> C.tmlit <*> return LUndefined
int = C.tmlit <*> (LNat . fromInteger <$> natural)
bool = C.tmlit <*> (LBool <$> (true <|> false)) where
  true = reserved "True" >> return True
  false = reserved "False" >> return False


parseParsedTerm :: String -> Either ParseError ParsedTerm
parseParsedTerm p = parse term "FRP" p
