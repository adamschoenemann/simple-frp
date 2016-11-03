
module FRP.AST where

import FRP.Pretty

type Name = String
type Pointer = String

data Type
  = TyParam Name
  | TyProd Type Type
  | TySum Type Type
  | TyArr Type Type
  | TyNext Type
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
    TyArr ty ty'  -> ppr n ty <+> text "->" <+> ppr n ty'
    TyNext ty     -> text "∙" <+> ppr n ty
    TyStable ty   -> text "☐" <+> ppr n ty
    TyStream ty   -> text "S" <+> ppr n ty
    TyAlloc       -> text "alloc"
    TyNat         -> text "Nat"

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
  | TmDelay Term Term
  | TmPromote Term
  | TmLet Pattern Term Term
  | TmLit Lit
  | TmBinOp BinOp Term Term
  | TmITE Term Term Term
  | TmPntr Pointer
  | TmPntrDeref Pointer
  | TmAlloc
  deriving (Show)

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
    TmLam b trm          -> text "\\" <> text b <> char '.' <+> ppr (n+1) trm
    TmVar v              -> text v
    TmApp trm trm'       -> ppr (n+1) trm <+> ppr (n+1) trm'
    TmCons hd tl         -> text "cons" <+> parens (ppr (n+1) hd <> comma <+> ppr (n+1) tl)
    TmDelay alloc trm    -> text "δ_" <> ppr (n+1) alloc <> parens (ppr (n+1) trm)
    TmPromote trm        -> text "promote" <> parens (ppr (n+1) trm)
    TmLet ptn trm trm'   -> text "let" <+> ppr (n+1) ptn <+> text "="
                              <+> ppr (n+1) trm <+> text "in" $$ ppr (n+1) trm'
    TmLit l              -> ppr n l
    TmBinOp op l r       -> ppr (n+1) l <+> ppr n op <+> ppr (n+1) r
    TmITE b trmt trmf    ->
      text "if" <+> ppr n b
        <+> text "then" <+> ppr (n+1) trmt
        <+> text "else" <+> ppr (n+1) trmf

data Value
  = VTup Value Value
  | VInl Value
  | VInr Value
  | VLam Name Term
  | VPntr Pointer
  | VAlloc
  | VStable Value
  | VCons Value Value
  deriving (Show)

data Pattern
  = PBind Name
  | PCons Pattern Pattern
  | PDelay Pattern
  | PStable Pattern
  deriving (Show)

instance Pretty Pattern where
  ppr n pat = case pat of
    PBind nm      -> text nm
    PCons p1 p2 -> text "cons" <> parens (ppr (n+1) p1 <> comma <+> ppr (n+1) p2)
    PDelay p1   -> text "δ" <> parens (ppr (n+1) p1)
    PStable p1    -> text "stable" <> parens (ppr (n+1) p1)


data BinOp
  = Add
  | Sub
  | Mult
  | Div
  | And
  | Or
  | Neg
  | Leq
  | Lt
  | Geq
  | Gt
  | Eq
  deriving (Show)

instance Pretty BinOp where
  ppr n op = text $ case op of
    Add  -> "+"
    Sub  -> "-"
    Mult -> "*"
    Div  -> "/"
    And  -> "&&"
    Or   -> "||"
    Neg  -> "!"
    Leq  -> "<="
    Lt   -> "<"
    Geq  -> ">="
    Gt   -> ">"
    Eq   -> "=="


data Lit
  = LInt Int
  | LBool Bool
  deriving (Show)

instance Pretty Lit where
  ppr n lit = case lit of
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
    text nm <+> char ':' <+> ppr n ty
      $$ text nm <+> char '=' <+> ppr n bd

data Program = Program { _main :: Decl, _decls :: [Decl]}
  deriving (Show)
