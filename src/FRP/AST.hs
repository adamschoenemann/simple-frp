{-# LANGUAGE DeriveFunctor             #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE DeriveDataTypeable        #-}
{-# LANGUAGE NamedFieldPuns            #-}


module FRP.AST where


import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import           Data.Set (Set)
import qualified Data.Set as S

import           Data.String     (IsString (..))
import           FRP.Pretty
import           Data.Data

type Name = String
type Label = Int
type EvalTerm = Term ()
type Env = Map String (Either EvalTerm Value)

initEnv :: Env
initEnv = M.empty

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
  = TyVar    a Name
  | TyProd   a (Type a) (Type a)
  | TySum    a (Type a) (Type a)
  | TyArr    a (Type a) (Type a)
  | TyLater  a (Type a)
  | TyStable a (Type a)
  | TyStream a (Type a)
  | TyRec    a Name (Type a)
  | TyAlloc  a
  | TyPrim   a TyPrim
  deriving (Show, Eq, Functor, Data, Typeable)

data TyPrim = TyBool | TyNat deriving (Show, Eq, Data, Typeable)

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
    TyPrim   _a TyNat  -> text "Nat"
    TyPrim   _a TyBool -> text "Bool"
    where
      prns = if (n > 0)
             then parens
             else id

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

data Term a
  = TmFst a (Term a)
  | TmSnd a (Term a)
  | TmTup a (Term a) (Term a)
  | TmInl a (Term a)
  | TmInr a (Term a)
  | TmCase a (Term a) (Name, (Term a)) (Name, (Term a))
  | TmLam a Name (Maybe (Type a)) (Term a)
  | TmVar a Name
  | TmApp  a (Term a) (Term a)
  | TmCons a (Term a) (Term a)
  | TmOut  a (Type a) (Term a)
  | TmInto a (Type a) (Term a)
  | TmStable a (Term a)
  | TmDelay  a (Term a) (Term a)
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

  bindings = \case
    PBind  nm       -> S.singleton nm
    PDelay nm       -> S.singleton nm
    PCons pat1 pat2 -> bindings pat1 +++ bindings pat2
    PStable pat     -> bindings pat
    PTup pat1 pat2  -> bindings pat1 +++ bindings pat2

-- not used right now, but useful later maybe
boundTyVarsTm :: Term a -> [Name]
boundTyVarsTm = S.toList . go where
  go = \case
    TmFst a t                    -> go t
    TmSnd a t                    -> go t
    TmTup a t1 t2                -> go t1 +++ go t2
    TmInl a t                    -> go t
    TmInr a t                    -> go t
    TmCase a t (ln, lt) (rn, rt) -> (go lt) +++ (go rt)
    TmLam a nm mty t             -> go t
    TmVar a nm                   -> S.empty
    TmApp a  t1 t2               -> go t1 +++ go t2
    TmCons a t1 t2               -> go t1 +++ go t2
    TmOut a  ty t                -> S.fromList $ boundTyVarsTy ty
    TmInto a _ t                 -> go t
    TmStable a t                 -> go t
    TmDelay a t1 t2              -> go t1 +++ go t2
    TmPromote a t                -> go t
    TmLet a pat t1 t2            -> go t1 +++ go t2
    TmLit a l                    -> S.empty
    TmBinOp a op t1 t2           -> go t1 +++ go t2
    TmITE a b tt tf              -> go b +++ go tt +++ go tf
    TmPntr a lbl                 -> S.empty
    TmPntrDeref a lbl            -> S.empty
    TmAlloc a                    -> S.empty
    TmFix a nm mty t             -> go t

  (+++) = S.union

-- not used right now, but useful later maybe
boundTyVarsTy :: Type a -> [Name]
boundTyVarsTy = S.toList . go where
  go = \case
    TyVar    _ name   -> S.empty
    TyProd   _ l r    -> go l  +++ go r
    TySum    _ l r    -> go l  +++ go r
    TyArr    _ t1 t2  -> go t1 +++ go t2
    TyLater  _ ty     -> go ty
    TyStable _ ty     -> go ty
    TyStream _ ty     -> go ty
    TyRec    _ nm ty  -> S.singleton nm
    TyAlloc  _        -> S.empty
    TyPrim{}          -> S.empty

  (+++) = S.union


instance Pretty (Map String (Either (Term a) Value)) where
  ppr n env = char '[' $+$ nest 2 body $+$ char ']' where
    body = vcat $ punctuate (char ',') $
      map (\(k,v) -> text k <+> text "↦" <+> ppr (n+1) v) $ M.toList env

instance IsString (EvalTerm) where
  fromString x = TmVar () x

instance IsString (Type ()) where
  fromString x = TyVar () x

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

    TmPntr _a pntr          -> text "&[" <> int pntr <> text "]"
    TmPntrDeref _a pntr     -> text "*[" <> int pntr <> text "]"
    TmAlloc _a              -> text "<>"

    TmOut  _a ty trm        -> text "out" <+> parens (ppr 0 ty)
                               <+> prns (ppr (n) trm)
    TmInto _a ty trm        -> text "into" <+> parens (ppr 0 ty)
                               <+> prns (ppr (n) trm)
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
  VInto v          -> TmInto () undefined (valToTerm v)
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

data Program a = Program { _imports :: [String], _decls :: [Decl a] }
  deriving (Show, Eq, Functor, Data, Typeable)

instance Pretty (Program a) where
  ppr n (Program {_decls = decls}) =
    vcat (map (\d -> ppr n d <> char '\n') decls)

unitFunc :: Functor f => f a -> f ()
unitFunc = fmap (const ())

paramsToLams :: [String] -> EvalTerm -> EvalTerm
paramsToLams = foldl (\acc x y -> acc (TmLam () x Nothing y)) id

paramsToLams' :: a -> [(String, Maybe (Type a))] -> Term a -> Term a
paramsToLams' b = foldl (\acc (x,t) y -> acc (TmLam b x t y)) id

fixifyDecl :: Decl t -> Decl t
fixifyDecl decl@(Decl {_ann, _name, _type, _body}) =
  if _name `elem` freeVars _body
    then decl {_body = TmFix _ann _name (Just _type) _body}
    else decl

-- FIXME: Will only work if the name bound by fix is _name
unfixifyDecl :: Decl t -> Decl t
unfixifyDecl decl@(Decl {_ann, _name, _type, _body}) =
  case _body of
    TmFix _a nm mty bd ->
      if nm == _name
        then decl {_body = bd}
        else decl
    _                  -> decl