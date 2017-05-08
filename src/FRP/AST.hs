{-|
Module      : FRP.AST
Description : Abstract Syntax Tree

This module implements the AST of FRP programs
-}
{-# LANGUAGE DeriveFunctor             #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE DeriveDataTypeable        #-}
{-# LANGUAGE NamedFieldPuns            #-}


module FRP.AST (
    Name
  , Label
  , EvalTerm
  , Env
  , initEnv
  , Qualifier(..)
  , Type(..)
  , isStable
  , typeAnn
  , TyPrim(..)
  , Term(..)
  , Lit(..)
  , Pattern(..)
  , Value(..)
  , valToTerm
  , BinOp(..)
  , Decl(..)
  , Program(..)
  , paramsToLams
  , fixifyDecl
  , unitFunc
  ) where

import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import           Data.Set (Set)
import qualified Data.Set as S

import           Data.String     (IsString (..))
import           FRP.Pretty
import           Data.Data

-- |A Name is just a String for now
type Name = String

-- |A pointer label is just an Integer
type Label = Integer
-- -----------------------------------------------------------------------------
-- EvalTerm
-- -----------------------------------------------------------------------------

-- |A Term for evaluation is just annotated with unit
type EvalTerm = Term ()
instance IsString (EvalTerm) where
  fromString x = TmVar () x

instance Num (EvalTerm) where
  fromInteger = TmLit () . LNat . fromInteger
  x + y = TmBinOp () Add x y
  x * y = TmBinOp () Mult x y
  x - y = TmBinOp () Sub x y
  abs _x = undefined
  signum = undefined

-- -----------------------------------------------------------------------------
-- Env
-- -----------------------------------------------------------------------------

-- |An evaluation environment is map from name to either
-- a term (lazy eval) or a value (strict)
type Env = Map String (Either EvalTerm Value)

instance Pretty (Map String (Either (Term a) Value)) where
  ppr n env = char '[' $+$ nest 2 body $+$ char ']' where
    body = vcat $ punctuate (char ',') $
      map (\(k,v) -> text k <+> text "↦" <+> ppr (n+1) v) $ M.toList env

-- |The initial environment
initEnv :: Env
initEnv = M.empty


-- -----------------------------------------------------------------------------
-- Qualifier
-- -----------------------------------------------------------------------------

-- |A Qualifier qualifies a value as being available now,
-- always (stable) or later
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

-- -----------------------------------------------------------------------------
-- Type
-- -----------------------------------------------------------------------------

infixr 9 `TyArr`

-- |A Type in the FRP language
data Type a
  -- |Type variable
  = TyVar    a Name
  -- |Product type
  | TyProd   a (Type a) (Type a)
  -- |Sum type
  | TySum    a (Type a) (Type a)
  -- |Arrow (function) type
  | TyArr    a (Type a) (Type a)
  -- |Later type
  | TyLater  a (Type a)
  -- |Stable type
  | TyStable a (Type a)
  -- |Type of streams
  | TyStream a (Type a)
  -- |Recursive types
  | TyRec    a Name (Type a)
  -- |Type of allocator tokens
  | TyAlloc  a
  -- |Primitive types
  | TyPrim   a TyPrim
  deriving (Show, Eq, Functor, Data, Typeable)

instance IsString (Type ()) where
  fromString x = TyVar () x

instance Pretty (Type a) where
  ppr n type' = case type' of
    TyVar  _a name     -> text name
    TyProd   _a ty ty' -> prns (ppr (n+1) ty <+> text "*" <+> ppr (n+1) ty')
    TySum    _a ty ty' -> prns (ppr (n+1) ty <+> text "+" <+> ppr (n+1) ty')
    TyArr    _a ty ty' -> prns $ ppr (n+1) ty <+> text "->" <+> ppr 0 ty'
    TyLater  _a ty     -> text "@" <> ppr (n+1) ty
    TyStable _a ty     -> text "#" <> ppr (n+1) ty
    TyStream _a ty     -> prns $ char 'S' <+> ppr (n+1) ty
    TyRec    _a nm ty  -> prns $ text "mu" <+> text nm <> char '.' <+> ppr 0 ty
    TyAlloc  _a        -> text "alloc"
    TyPrim   _a p      -> ppr n p
    where
      prns = if (n > 0)
             then parens
             else id

-- |Get the annotation of a type (typically position in source)
typeAnn :: Type a -> a
typeAnn = \case
    TyVar    a _   -> a
    TyProd   a _ _ -> a
    TySum    a _ _ -> a
    TyArr    a _ _ -> a
    TyLater  a _   -> a
    TyStable a _   -> a
    TyStream a _   -> a
    TyRec    a _ _ -> a
    TyAlloc  a     -> a
    TyPrim   a _   -> a

-- |Checks if a 'Type' is Stable
isStable :: Type t -> Bool
isStable (TyPrim _ _ )  = True
isStable (TyProd _ a b) = isStable a && isStable b
isStable (TySum  _ a b) = isStable a && isStable b
isStable (TyStable _ _) = True
isStable _              = False

-- |Primitive types (bool, nat or unit)
data TyPrim = TyBool | TyNat | TyUnit | TyBot deriving (Show, Eq, Data, Typeable)

instance Pretty TyPrim where
  ppr n = text . \case
    TyBool -> "Bool"
    TyNat  -> "Nat"
    TyUnit -> "()"
    TyBot  -> "_|_"

-- -----------------------------------------------------------------------------
-- Term
-- -----------------------------------------------------------------------------

-- |Terms in the FRP language
data Term a
  -- |fst
  = TmFst a (Term a)
  -- |snd
  | TmSnd a (Term a)
  -- |A tuple
  | TmTup a (Term a) (Term a)
  -- |Left injection
  | TmInl a (Term a)
  -- |Right injection
  | TmInr a (Term a)
  -- |Case pattern match
  | TmCase a (Term a) (Name, (Term a)) (Name, (Term a))
  -- |A lambda
  | TmLam a Name (Maybe (Type a)) (Term a)
  -- |A variable use
  | TmVar a Name
  -- |Application of a term to another term
  | TmApp  a (Term a) (Term a)
  -- |Stream Cons
  | TmCons a (Term a) (Term a)
  -- |@out@ for recursive type elimination
  | TmOut  a (Type a) (Term a)
  -- |@into@ for recursive type introduction
  | TmInto a (Type a) (Term a)
  -- |Attempt to make a value stable
  | TmStable a (Term a)
  -- |Delay a value with an allocation token
  | TmDelay  a (Term a) (Term a)
  -- |Promote a term of a stable type
  | TmPromote a (Term a)
  -- |A let binding with a a pattern
  | TmLet a Pattern (Term a) (Term a)
  -- |A value-level literal
  | TmLit a Lit
  -- |A binary operation
  | TmBinOp a BinOp (Term a) (Term a)
  -- |If-then-else
  | TmITE a (Term a) (Term a) (Term a)
  -- |A pointer (not syntactic)
  | TmPntr a Label
  -- |A pointer dereference (not syntactic)
  | TmPntrDeref a Label
  -- |An allocator token
  | TmAlloc a
  -- |A fixpoint!
  | TmFix a Name (Maybe (Type a)) (Term a)
  deriving (Show, Eq, Functor, Data, Typeable)

instance Pretty (Term a) where
  ppr n term = case term of
    TmFst  _a trm            -> text "fst" <+> ppr (n+1) trm
    TmSnd  _a trm            -> text "snd" <+> ppr (n+1) trm
    TmTup  _a trm trm'       -> parens $ ppr (n+1) trm <> comma <+> ppr (n+1) trm'
    TmInl  _a trm            -> text "inl" <+> prns (ppr (n+1) trm)
    TmInr  _a trm            -> text "inr" <+> prns (ppr (n+1) trm)

    TmCase _a trm (vl, trml) (vr, trmr) ->
      text "case" <+> ppr 0 trm <+> text "of"
        $$ nest (2) (text "| inl" <+> text vl <+> text "->" <+> ppr (0) trml)
        $$ nest (2) (text "| inr" <+> text vr <+> text "->" <+> ppr (0) trmr)

    TmLam _a b mty trm      ->
      let pty = maybe mempty (\t -> char ':' <> ppr 0 t) mty
          maybePrns = maybe id (const parens) mty
      in  prns (text "\\" <> maybePrns (text b <> pty) <+> text "->" <+> ppr (n) trm)

    TmFix _a b ty trm       -> prns (text "fix" <+> text b <> char '.' <+> ppr (n+1) trm)
    TmVar _a v              -> text v
    TmApp _a trm trm'       -> prns (ppr 0 trm <+> ppr (n+1) trm')
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

    TmPntr _a pntr          -> text "&[" <> integer pntr <> text "]"
    TmPntrDeref _a pntr     -> text "*[" <> integer pntr <> text "]"
    TmAlloc _a              -> text "<>"

    TmOut  _a ty trm        -> text "out" <+> parens (ppr 0 ty)
                               <+> prns (ppr (n) trm)
    TmInto _a ty trm        -> text "into" <+> parens (ppr 0 ty)
                               <+> prns (ppr (n) trm)
    where
      prns = if (n > 0)
             then parens
             else id

-- |Get the free variables in a term
freeVars :: Term a -> [Name]
freeVars = S.toList . go where
  go = \case
    TmFst a t                    -> go t
    TmSnd a t                    -> go t
    TmTup a t1 t2                -> go t1 +++ go t2
    TmInl a t                    -> go t
    TmInr a t                    -> go t
    TmCase a t (ln, lt) (rn, rt) -> (go lt // ln) +++ (go rt // rn)
    TmLam a nm mty t             -> go t // nm
    TmVar a nm                   -> S.singleton nm
    TmApp a  t1 t2               -> go t1 +++ go t2
    TmCons a t1 t2               -> go t1 +++ go t2
    TmOut a  _ t                 -> go t
    TmInto a _ t                 -> go t
    TmStable a t                 -> go t
    TmDelay a t1 t2              -> go t1 +++ go t2
    TmPromote a t                -> go t
    TmLet a pat t1 t2            -> (go t1 +++ go t2) \\ bindings pat
    TmLit a l                    -> S.empty
    TmBinOp a op t1 t2           -> go t1 +++ go t2
    TmITE a b tt tf              -> go b +++ go tt +++ go tf
    TmPntr a lbl                 -> S.empty
    TmPntrDeref a lbl            -> S.empty
    TmAlloc a                    -> S.empty
    TmFix a nm mty t             -> go t // nm

  (+++) = S.union
  (//)  = flip S.delete
  (\\)  = (S.\\)

  -- Get the bindings in a pattern
  bindings = \case
    PBind  nm       -> S.singleton nm
    PDelay nm       -> S.singleton nm
    PCons pat1 pat2 -> bindings pat1 +++ bindings pat2
    PStable pat     -> bindings pat
    PTup pat1 pat2  -> bindings pat1 +++ bindings pat2

-- -----------------------------------------------------------------------------
-- Value
-- -----------------------------------------------------------------------------

-- |A Value is a term that is evaluated to normal form
data Value
  -- |A tuple
  = VTup Value Value
  -- |Left injection
  | VInl Value
  -- |Right injection
  | VInr Value
  -- |A closure
  | VClosure Name EvalTerm Env
  -- |A pointer
  | VPntr Label
  -- |An allocation token
  | VAlloc
  -- |A stable value
  | VStable Value
  -- |A value of a recursive type
  | VInto Value
  -- |A stream Cons
  | VCons Value Value
  -- |A value literal
  | VLit Lit
  deriving (Show, Eq, Data, Typeable)

-- Convert a value back into a term
valToTerm :: Value -> EvalTerm
valToTerm = \case
  VTup a b         -> TmTup () (valToTerm a) (valToTerm b)
  VInl v           -> TmInl () (valToTerm v)
  VInr v           -> TmInr () (valToTerm v)
  VClosure x e env -> TmLam () x Nothing (fmap (const ()) e)
  VPntr l          -> TmPntr () l
  VAlloc           -> TmAlloc ()
  VStable v        -> TmStable () (valToTerm v)
  VInto v          -> TmInto () undefined (valToTerm v)
  VCons hd tl      -> TmCons () (valToTerm hd) (valToTerm tl)
  VLit l           -> TmLit () l

instance Pretty Value where
  ppr x = ppr x . valToTerm

-- -----------------------------------------------------------------------------
-- Pattern
-- -----------------------------------------------------------------------------

-- |A Pattern used in a let binding
data Pattern
  = PBind Name            -- ^Bind a name
  | PDelay Name           -- ^Bind a delayed name
  | PCons Pattern Pattern -- ^Match on a Cons cell
  | PStable Pattern       -- ^Match on a stable value
  | PTup Pattern Pattern  -- ^Match on tuple
  deriving (Show, Eq, Data, Typeable)

instance Pretty Pattern where
  ppr n pat = case pat of
    PBind nm      -> text nm
    PCons p1 p2   -> text "cons" <> parens (ppr (n+1) p1 <> comma <+> ppr (n+1) p2)
    PDelay p1     -> text "delay" <> parens (text p1)
    PStable p1    -> text "stable" <> parens (ppr (n+1) p1)
    PTup p1 p2    -> char '(' <> ppr 0 p1 <> char ',' <+> ppr 0 p2 <> char ')'

instance IsString Pattern where
  fromString x = PBind x

-- -----------------------------------------------------------------------------
-- BinOp
-- -----------------------------------------------------------------------------

-- |A binary operator
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


-- -----------------------------------------------------------------------------
-- A value literal
-- -----------------------------------------------------------------------------
data Lit
  = LNat Int
  | LBool Bool
  | LUnit
  | LUndefined
  deriving (Show, Eq, Data, Typeable)

instance Pretty Lit where
  ppr _ lit = case lit of
    LNat  i -> if (i >= 0) then int i else parens (int i)
    LBool b -> text $ show b
    LUnit   -> text "()"
    LUndefined   -> text "undefined"

-- -----------------------------------------------------------------------------
-- Decl
-- -----------------------------------------------------------------------------

-- |A declaration has an annotation, a type, a name and a body that is a term
data Decl a =
  Decl { _ann  :: a
       , _type :: Type a
       , _name :: Name
       , _body :: Term a
       }
       deriving (Show, Eq, Functor, Data, Typeable)

instance Pretty (Decl a) where
  ppr n = go n . unfixifyDecl where
    go n (Decl _a ty nm bd) =
      let (bs, bd') = bindings bd
      in  text nm <+> char ':' <+> ppr n ty
          $$ hsep (map text (nm : bs)) <+> char '='
          $$ nest 2 (ppr 0 bd' <> char '.')
      where
        bindings (TmLam _a x _ b) =
          let (y, b') = bindings b
          in  (x:y, b')
        bindings b           = ([], b)

-- -----------------------------------------------------------------------------
-- Program
-- -----------------------------------------------------------------------------

-- |A Program is simply a list of declarations and a list of imports.
-- The imports are not used right now though (and cannot be parsed either)
data Program a = Program { _imports :: [String], _decls :: [Decl a] }
  deriving (Show, Eq, Functor, Data, Typeable)

instance Pretty (Program a) where
  ppr n (Program {_decls = decls}) =
    vcat (map (\d -> ppr n d <> char '\n') decls)

-- -----------------------------------------------------------------------------
-- Utility functions
-- -----------------------------------------------------------------------------

-- |Convert any functor to a unit-functor
unitFunc :: Functor f => f a -> f ()
unitFunc = fmap (const ())


-- |Desugar a multi-parameter lambda to nested lambdas
-- @\x y z -> x (y z)@  becomes
-- @\x -> \y -> \z -> x (y z)$
paramsToLams :: a -> [(String, Maybe (Type a))] -> Term a -> Term a
paramsToLams b = foldl (\acc (x,t) y -> acc (TmLam b x t y)) id

-- |Desugar a recursive definition to a fixpoint
fixifyDecl :: Decl t -> Decl t
fixifyDecl decl@(Decl {_ann, _name, _type, _body}) =
  if _name `elem` freeVars _body
    then decl {_body = TmFix _ann _name (Just _type) _body}
    else decl

-- |Convert a fixpoint back into a recursive definition
-- FIXME: Will only work if the name bound by fix is _name
unfixifyDecl :: Decl t -> Decl t
unfixifyDecl decl@(Decl {_ann, _name, _type, _body}) =
  case _body of
    TmFix _a nm mty bd ->
      if nm == _name
        then decl {_body = bd}
        else decl
    _                  -> decl