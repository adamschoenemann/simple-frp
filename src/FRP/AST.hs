{-# LANGUAGE DeriveFunctor             #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE StandaloneDeriving        #-}
{-# LANGUAGE DeriveDataTypeable        #-}


module FRP.AST where


import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import           Data.String     (IsString (..))
import           FRP.Pretty
import           Data.Data

type Name = String
type Label = Int
type EvalTerm = Term ()
type Env = Map String (Either EvalTerm Value)

data Qualifier
  = QNow
  | QStable
  | QLater
  deriving (Show, Eq, Data, Typeable)

instance Pretty Qualifier where
  ppr n = \case
    QNow    -> text "now"
    QStable -> text "stable"
    QLater  -> text "later"

infixr 9 `TyArr`

data Type a
  = TyParam  a Name
  | TyProd   a (Type a) (Type a)
  | TySum    a (Type a) (Type a)
  | TyArr    a (Type a) (Type a)
  | TyLater  a (Type a)
  | TyStable a (Type a)
  | TyStream a (Type a)
  | TyAlloc  a
  | TyNat    a
  | TyBool   a
  deriving (Show, Eq, Functor, Data, Typeable)

instance Pretty (Type a) where
  ppr n type' = case type' of
    TyParam  _a name   -> text name
    TyProd   _a ty ty' -> prns (ppr (n+1) ty <+> text "*" <+> ppr (n+1) ty')
    TySum    _a ty ty' -> prns (ppr (n+1) ty <+> text "+" <+> ppr (n+1) ty')
    TyArr    _a ty ty' -> prns $ ppr n ty <+> text "->" <+> ppr n ty'
    TyLater  _a ty     -> text "@" <> ppr (n+1) ty
    TyStable _a ty     -> text "#" <> ppr (n+1) ty
    TyStream _a ty     -> prns $ text "S" <+> ppr (n+1) ty
    TyAlloc  _a        -> text "alloc"
    TyNat    _a        -> text "Nat"
    TyBool   _a        -> text "Bool"
    where
      prns = if (n > 0)
             then parens
             else id

data Term a
  = TmFst a (Term a)
  | TmSnd a (Term a)
  | TmTup a (Term a) (Term a)
  | TmInl a (Term a)
  | TmInr a (Term a)
  | TmCase a (Term a) (Name, (Term a)) (Name, (Term a))
  | TmLam a Name (Maybe (Type a)) (Term a)
  | TmVar a Name
  | TmApp a (Term a) (Term a)
  | TmCons a (Term a) (Term a)
  | TmOut a (Term a)
  | TmInto a (Term a)
  | TmStable a (Term a)
  | TmDelay a (Term a) (Term a)
  | TmPromote a (Term a)
  | TmLet a Pattern (Term a) (Term a)
  | TmLit a Lit
  | TmBinOp a BinOp (Term a) (Term a)
  | TmITE a (Term a) (Term a) (Term a)
  | TmPntr a Label
  | TmPntrDeref a Label
  | TmAlloc a
  | TmFix a Name (Maybe (Type a)) (Term a)
  deriving (Show, Eq, Functor, Data, Typeable)


instance Pretty (Map String (Either (Term a) Value)) where
  ppr n env = char '[' $+$ nest 2 body $+$ char ']' where
    body = vcat $ punctuate (char ',') $
      map (\(k,v) -> text k <+> text "↦" <+> ppr (n+1) v) $ M.toList env

instance IsString (EvalTerm) where
  fromString x = TmVar () x

instance IsString (Type ()) where
  fromString x = TyParam () x

instance IsString Pattern where
  fromString x = PBind x

instance Pretty (Term a) where
  ppr n term = case term of
    TmFst _a trm            -> text "fst" <+> ppr (n+1) trm
    TmSnd _a trm            -> text "snd" <+> ppr (n+1) trm
    TmTup _a trm trm'       -> parens $ ppr (n+1) trm <> comma <+> ppr (n+1) trm'
    TmInl _a trm            -> text "inl" <+> prns (ppr (n+1) trm)
    TmInr _a trm            -> text "inr" <+> prns (ppr (n+1) trm)
    TmCase _a trm (vl, trml) (vr, trmr) ->
      text "case" <+> ppr 0 trm <+> text "of"
        $$ nest (2) (text "| inl" <+> text vl <+> text "->" <+> ppr (0) trml)
        $$ nest (2) (text "| inr" <+> text vr <+> text "->" <+> ppr (0) trmr)
    TmLam _a b mty trm      ->
      let pty = maybe mempty (\t -> char ':' <> ppr 0 t) mty
          maybePrns = maybe id (const parens) mty
      in  prns (text "\\" <> maybePrns (text b <> pty) <+> text "->" <+> ppr (n) trm)
    TmFix _a b ty trm       -> prns (text "fix" <+> text b <+> text "->" <+> ppr (n+1) trm)
    TmVar _a v              -> text v
    TmApp _a trm trm'       -> parens (ppr 0 trm <+> ppr (n+1) trm')
    TmCons _a hd tl         -> text "cons" <> parens (ppr (n+1) hd <> comma <+> ppr (n+1) tl)
    TmDelay _a alloc trm    -> text "delay" <> parens (ppr 0 alloc <> comma <+> ppr 0 trm)
    TmStable _a trm         -> text "stable" <> parens (ppr 0 trm)
    TmPromote _a trm        -> text "promote" <> parens (ppr 0 trm)
    TmLet _a ptn trm trm'   -> text "let" <+> ppr (0) ptn <+> text "="
                              <+> ppr (n) trm <+> text "in" $$ ppr (0) trm'
    TmLit _a l              -> ppr n l
    TmBinOp _a op l r       -> prns (ppr (n+1) l <+> ppr n op <+> ppr (n+1) r)
    TmITE _a b trmt trmf    ->
      text "if" <+> ppr n b
        $$ nest 2 (text "then" <+> ppr (n+1) trmt)
        $$ nest 2 (text "else" <+> ppr (n+1) trmf)
    TmPntr _a pntr          -> text "&[" <> int pntr <> text "]"
    TmPntrDeref _a pntr     -> text "*[" <> int pntr <> text "]"
    TmAlloc _a              -> text "¤"
    TmOut _a trm            -> text "out"  <+> prns (ppr (n) trm)
    TmInto _a trm           -> text "into" <+> prns (ppr (n) trm)
    where
      prns = if (n > 0)
             then parens
             else id

instance Num (EvalTerm) where
  fromInteger = TmLit () . LInt . fromInteger
  x + y = TmBinOp () Add x y
  x * y = TmBinOp () Mult x y
  x - y = TmBinOp () Sub x y
  abs _x = undefined
  signum = undefined

data Value
  = VTup Value Value
  | VInl Value
  | VInr Value
  | VClosure Name EvalTerm Env
  | VPntr Label
  | VAlloc
  | VStable Value
  | VInto Value
  | VCons Value Value
  | VLit Lit
  deriving (Show, Eq, Data, Typeable)

valToTerm :: Value -> EvalTerm
valToTerm = \case
  VTup a b         -> TmTup () (valToTerm a) (valToTerm b)
  VInl v           -> TmInl () (valToTerm v)
  VInr v           -> TmInr () (valToTerm v)
  VClosure x e env -> TmLam () x Nothing (fmap (const ()) e)
  VPntr l          -> TmPntr () l
  VAlloc           -> TmAlloc ()
  VStable v        -> TmStable () (valToTerm v)
  VInto v          -> TmInto () (valToTerm v)
  VCons hd tl      -> TmCons () (valToTerm hd) (valToTerm tl)
  VLit l           -> TmLit () l

instance Pretty Value where
  ppr x = ppr x . valToTerm


data Pattern
  = PBind Name
  | PDelay Name
  | PCons Pattern Pattern
  | PStable Pattern
  | PTup Pattern Pattern
  deriving (Show, Eq, Data, Typeable)

instance Pretty Pattern where
  ppr n pat = case pat of
    PBind nm      -> text nm
    PCons p1 p2   -> text "cons" <> parens (ppr (n+1) p1 <> comma <+> ppr (n+1) p2)
    PDelay p1     -> text "delay" <> parens (text p1)
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
  deriving (Show, Eq, Data, Typeable)

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
  deriving (Show, Eq, Data, Typeable)

instance Pretty Lit where
  ppr _ lit = case lit of
    LInt  i -> if (i >= 0) then int i else parens (int i)
    LBool b -> text $ show b

data Decl a =
  Decl { _ann  :: a
       , _type :: Type a
       , _name :: Name
       , _body :: Term a
       }
       deriving (Show, Eq, Functor, Data, Typeable)


instance Pretty (Decl a) where
  ppr n (Decl _a ty nm bd) =
    let (bs, bd') = bindings bd
    in  text nm <+> char ':' <+> ppr n ty
        $$ hsep (map text (nm : bs)) <+> char '=' $$ nest 2 (ppr n bd' <> char '.')
    where
      bindings (TmLam _a x _ b) =
        let (y, b') = bindings b
        in  (x:y, b')
      bindings b           = ([], b)

data Program a = Program { _main :: Decl a, _decls :: [Decl a]}
  deriving (Show, Eq, Functor, Data, Typeable)

instance Pretty (Program a) where
  ppr n (Program main decls) =
    vcat (map (\d -> ppr n d <> char '\n') (decls ++ [main]))

unitFunc :: Functor f => f a -> f ()
unitFunc = fmap (const ())

paramsToLams :: [String] -> EvalTerm -> EvalTerm
paramsToLams = foldl (\acc x y -> acc (TmLam () x Nothing y)) id

paramsToLams' :: a -> [(String, Maybe (Type a))] -> Term a -> Term a
paramsToLams' b = foldl (\acc (x,t) y -> acc (TmLam b x t y)) id
