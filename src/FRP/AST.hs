{-# LANGUAGE FlexibleInstances #-}

module FRP.AST where


import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import FRP.Pretty
import Data.String (IsString(..))

type Name = String
type Label = Int
type Env = Map String (Either Term Value)

data Type
  = TyParam Name
  | TyProd Type Type
  | TySum Type Type
  | TyArr Type Type
  | TyLater Type
  | TyStable Type
  | TyStream Type
  | TyAlloc
  | TyNat
  deriving (Show)

instance Pretty Type where
  ppr n type' = case type' of
    TyParam name  -> text name
    TyProd ty ty' -> parens (ppr (n+1) ty <+> text "×" <+> ppr (n+1) ty')
    TySum ty ty'  -> parens (ppr (n+1) ty <+> text "+" <+> ppr (n+1) ty')
    TyArr ty ty'  -> prns $ ppr n ty <+> text "->" <+> ppr n ty'
    TyLater ty    -> prns $ text "∙" <> ppr (n+1) ty
    TyStable ty   -> prns $ text "☐" <> ppr (n+1) ty
    TyStream ty   -> prns $ text "S" <+> ppr (n+1) ty
    TyAlloc       -> text "alloc"
    TyNat         -> text "Nat"
    where
      prns = if (n > 0)
             then parens
             else id

infixl 9 `TmApp`
infixr 9 `TyArr`

data Term
  = TmFst Term
  | TmSnd Term
  | TmTup Term Term
  | TmInl Term
  | TmInr Term
  | TmCase Term (Name, Term) (Name, Term)
  | TmLam Name Term
  | TmVar Name
  | TmApp Term Term
  | TmCons Term Term
  | TmClosure Name Term Env
  | TmStable Term
  | TmDelay Term Term
  | TmPromote Term
  | TmLet Pattern Term Term
  | TmLit Lit
  | TmBinOp BinOp Term Term
  | TmITE Term Term Term
  | TmPntr Label
  | TmPntrDeref Label
  | TmAlloc
  | TmFix Name Term
  deriving (Show, Eq)

instance Pretty (Either Term Value) where
  ppr n (Left t) = ppr n t
  ppr n (Right v) = ppr n v

instance Pretty (Map String (Either Term Value)) where
  ppr n env = char '[' $+$ nest 2 body $+$ char ']' where
    body = vcat $ punctuate (char ',') $
      map (\(k,v) -> text k <+> text "↦" <+> ppr (n+1) v) $ M.toList env

instance IsString Term where
  fromString x = TmVar x

instance IsString Type where
  fromString x = TyParam x

instance IsString Pattern where
  fromString x = PBind x

instance Pretty Term where
  ppr n term = case term of
    TmFst trm            -> text "fst" <+> ppr (n+1) trm
    TmSnd trm            -> text "snd" <+> ppr (n+1) trm
    TmTup trm trm'       -> parens $ ppr (n+1) trm <+> comma <+> ppr (n+1) trm'
    TmInl trm            -> text "inl" <+> ppr (n+1) trm
    TmInr trm            -> text "inr" <+> ppr (n+1) trm
    TmCase trm (vl, trml) (vr, trmr) ->
      text "case" <+> parens (ppr (n+1) trm <+> comma
        <+> text "inl" <+> text vl <+> text "->" <+> ppr (n+1) trml
        <+> text "inr" <+> text vr <+> text "->" <+> ppr (n+1) trmr)
    TmLam b trm          -> prns (text "\\" <> text b <> char '.' <+> ppr (n+1) trm)
    TmFix b trm          -> prns (text "fix" <+> text b <> char '.' <+> ppr (n+1) trm)
    TmClosure b trm env  -> ppr n (TmLam b trm)-- prns $ ppr (n+1) (TmLam b trm) -- <> comma <+> ppr (n+1) env
    TmVar v              -> text v
    TmApp trm trm'       -> ppr (n+1) trm <+> ppr (n+1) trm'
    TmCons hd tl         -> text "cons" <> parens (ppr (n+1) hd <> comma <+> ppr (n+1) tl)
    TmDelay alloc trm    -> text "δ_" <> ppr (n+1) alloc <> parens (ppr 0 trm)
    TmStable trm         -> text "stable" <> parens (ppr 0 trm)
    TmPromote trm        -> text "promote" <> parens (ppr 0 trm)
    TmLet ptn trm trm'   -> text "let" <+> ppr (n+1) ptn <+> text "="
                              <+> ppr (n+1) trm <+> text "in" $$ ppr (n+1) trm'
    TmLit l              -> ppr n l
    TmBinOp op l r       -> prns (ppr (n+1) l <+> ppr n op <+> ppr (n+1) r)
    TmITE b trmt trmf    ->
      text "if" <+> ppr n b
        $$ nest 2 (text "then" <+> ppr (n+1) trmt)
        $$ nest 2 (text "else" <+> ppr (n+1) trmf)
    TmPntr pntr          -> text "&[" <> int pntr <> text "]"
    TmPntrDeref pntr     -> text "*[" <> int pntr <> text "]"
    TmAlloc              -> text "♢"
    where
      prns = if (n > 0)
             then parens
             else id

instance Num Term where
  fromInteger = TmLit . LInt . fromInteger
  x + y = TmBinOp Add x y
  x * y = TmBinOp Mult x y
  x - y = TmBinOp Sub x y
  abs x = undefined
  signum = undefined

data Value
  = VTup Value Value
  | VInl Value
  | VInr Value
  | VLam Name Term
  | VClosure Name Term Env
  | VPntr Label
  | VAlloc
  | VStable Value
  -- | VInto Value
  | VCons Value Value
  | VLit Lit
  deriving (Show, Eq)

valToTerm :: Value -> Term
valToTerm = \case
  VTup a b         -> TmTup (valToTerm a) (valToTerm b)
  VInl v           -> TmInl (valToTerm v)
  VInr v           -> TmInr (valToTerm v)
  VLam x e         -> TmLam x e
  VClosure x e env -> TmClosure x e env
  VPntr l          -> TmPntr l
  VAlloc           -> TmAlloc
  VStable v        -> TmStable (valToTerm v)
  -- VInto v          -> TmInto (valToTerm v)
  VCons hd tl      -> TmCons (valToTerm hd) (valToTerm tl)
  VLit l           -> TmLit l

instance Pretty Value where
  ppr x = ppr x . valToTerm


data Pattern
  = PBind Name
  | PDelay Name
  | PCons Pattern Pattern
  | PStable Pattern
  | PTup Pattern Pattern
  deriving (Show, Eq)

instance Pretty Pattern where
  ppr n pat = case pat of
    PBind nm      -> text nm
    PCons p1 p2   -> text "cons" <> parens (ppr (n+1) p1 <> comma <+> ppr (n+1) p2)
    PDelay p1     -> text "δ" <> parens (text p1)
    PStable p1    -> text "stable" <> parens (ppr (n+1) p1)
    PTup p1 p2    -> char '(' <> ppr 0 p1 <> char ',' <+> ppr 0 p2 <> char ')'


data BinOp
  = Add
  | Sub
  | Mult
  | Div
  | And
  | Or
  | Leq
  | Lt
  | Geq
  | Gt
  | Eq
  deriving (Show, Eq)

instance Pretty BinOp where
  ppr _ op = text $ case op of
    Add  -> "+"
    Sub  -> "-"
    Mult -> "*"
    Div  -> "/"
    And  -> "&&"
    Or   -> "||"
    Leq  -> "<="
    Lt   -> "<"
    Geq  -> ">="
    Gt   -> ">"
    Eq   -> "=="


data Lit
  = LInt Int
  | LBool Bool
  deriving (Show, Eq)

instance Pretty Lit where
  ppr _ lit = case lit of
    LInt  i -> int i
    LBool b -> text $ show b

data Decl =
  Decl { _type :: Type
       , _name :: Name
       , _body :: Term
       }
  deriving (Show)

instance Pretty Decl where
  ppr n (Decl ty nm bd) =
    let (bs, bd') = bindings bd
    in  text nm <+> char ':' <+> ppr n ty
        $$ hsep (map text (nm : bs)) <+> char '=' $$ nest 2 (ppr n bd')
    where
      bindings (TmLam x b) =
        let (y, b') = bindings b
        in  (x:y, b')
      bindings (TmClosure x b _) =
        let (y, b') = bindings b
        in  (x:y, b')
      bindings b           = ([], b)

data Program = Program { _main :: Decl, _decls :: [Decl]}
  deriving (Show)

instance Pretty Program where
  ppr n (Program main decls) = vcat (map (\d -> ppr n d <> char '\n') (decls ++ [main]))