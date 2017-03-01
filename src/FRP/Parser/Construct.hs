
module FRP.Parser.Construct where

import FRP.AST
import Text.Parsec
import Text.Parsec.String
import Text.Parsec.Pos

type ParsedTerm = Term SourcePos

tmfst :: Parser (ParsedTerm -> ParsedTerm)
tmfst = TmFst <$> getPosition

tmsnd :: Parser (ParsedTerm -> ParsedTerm)
tmsnd = TmSnd <$> getPosition

tmtup :: Parser (ParsedTerm -> ParsedTerm -> ParsedTerm)
tmtup = TmTup <$> getPosition

tminl :: Parser (ParsedTerm -> ParsedTerm)
tminl = TmInl <$> getPosition

tminr :: Parser (ParsedTerm -> ParsedTerm)
tminr = TmInr <$> getPosition

tmcase :: Parser (ParsedTerm -> (Name, ParsedTerm) -> (Name, ParsedTerm) -> ParsedTerm)
tmcase = TmCase <$> getPosition

tmlam :: Parser (Name -> (Maybe (Type SourcePos)) -> ParsedTerm -> ParsedTerm)
tmlam = TmLam <$> getPosition

tmvar :: Parser (Name -> ParsedTerm)
tmvar = TmVar <$> getPosition

tmapp :: Parser (ParsedTerm -> ParsedTerm -> ParsedTerm)
tmapp = TmApp <$> getPosition

tmcons :: Parser (ParsedTerm -> ParsedTerm -> ParsedTerm)
tmcons = TmCons <$> getPosition

tmout :: Parser (ParsedTerm -> ParsedTerm)
tmout = TmOut <$> getPosition

tminto :: Parser (ParsedTerm -> ParsedTerm)
tminto = TmInto <$> getPosition


tmstable :: Parser (ParsedTerm -> ParsedTerm)
tmstable = TmStable <$> getPosition

tmdelay :: Parser (ParsedTerm -> ParsedTerm -> ParsedTerm)
tmdelay = TmDelay <$> getPosition

tmpromote :: Parser (ParsedTerm -> ParsedTerm)
tmpromote = TmPromote <$> getPosition

tmlet :: Parser (Pattern -> ParsedTerm -> ParsedTerm -> ParsedTerm)
tmlet = TmLet <$> getPosition

tmlit :: Parser (Lit -> ParsedTerm)
tmlit = TmLit <$> getPosition

tmbinop :: Parser (BinOp -> ParsedTerm -> ParsedTerm -> ParsedTerm)
tmbinop = TmBinOp <$> getPosition

tmite :: Parser (ParsedTerm -> ParsedTerm -> ParsedTerm -> ParsedTerm)
tmite = TmITE <$> getPosition

tmpntr :: Parser (Label -> ParsedTerm)
tmpntr = TmPntr <$> getPosition

tmpntrderef :: Parser (Label -> ParsedTerm)
tmpntrderef = TmPntrDeref <$> getPosition

tmalloc :: Parser (ParsedTerm)
tmalloc = TmAlloc <$> getPosition

tmfix :: Parser (Name -> ParsedTerm -> ParsedTerm)
tmfix = TmFix <$> getPosition