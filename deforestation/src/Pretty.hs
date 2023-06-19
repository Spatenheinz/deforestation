{-# LANGUAGE FlexibleInstances, LambdaCase #-}
module Pretty where

import Type
import AST
import Data.Map (Map)
import qualified Data.Map.Strict as M
import Data.List (intercalate)
import Prettyprinter
import Prettyprinter.Util
import Infer (InferErr(..), Constraint(..))
import Check (ResolutionErr(..))
import Util (letters, compound)
import Eval (RuntimeErr(..), Value(..))

mkPretty :: Pretty e => e -> IO ()
mkPretty e = putDocW 80 (pretty e) >> putStrLn ""

debug :: Pretty e => e -> String
debug = show . pretty

data TypeOf = MkTo Expr Scheme

instance Pretty TypeOf where
  pretty (MkTo n t) = pretty n <+> pretty "::" <+> pretty t

instance Pretty Literal where
  pretty (LInt i) = pretty i
  pretty (LChar c) = pretty c
  pretty (LUnit) = pretty "()"

instance Pretty Op where
  pretty = \case
    Add -> pretty "+"
    Sub -> pretty "-"
    Mul -> pretty "*"
    Div -> pretty "/"
    -- Mod -> pretty "%"
    Eq -> pretty "=="
    Neq -> pretty "/="
    Lt -> pretty "<"
    Gt -> pretty ">"
    Leq -> pretty "<="
    Geq -> pretty ">="
    -- And -> pretty "&&"
    -- Or -> pretty "||"
    -- Not -> pretty "not"
    -- Neg -> pretty "negate"

instance Pretty Expr where
  pretty = \case
    Var v -> pretty v
    Lit l -> pretty l
    Lam x e -> hang 2 (pretty "λ" <> pretty x <+> pretty "->" <+> softline <> pretty e)
    App f@(Lam x b) e -> wrap (const True) f <+> wrap compound e
    App f e -> pretty f <+> wrap compound e
    Case e alts -> hang 2 (pretty "case" <+> pretty e <+> pretty "of"
                   <> hardline <> (vsep (map prettyAlt alts)))
    Con c -> pretty c -- <+> hsep (map pretty es)
    Prim op m n -> pretty "(" <> pretty m <+> pretty op <+> pretty n <> pretty ")"
    Blazed e -> wrap compound e <> pretty "⊖"


wrap :: Pretty a => (a -> Bool) -> a -> Doc ann
wrap f x = if f x then pretty "(" <> pretty x <> pretty ")" else pretty x

instance Pretty Pattern where
  pretty = \case
    VarAlt v -> pretty v
    LitAlt l -> pretty l
    WildCard -> pretty "_"
    ConAlt n ps -> group (pretty n <+> hsep (map pretty ps))
    PBlazed p -> pretty p <> pretty "⊖"

  -- We wanna split after -> if not possible to have
prettyAlt :: Alt -> Doc ann
prettyAlt (p, e) = hang 2 (pretty p <+> pretty "->" <+> softline <> (pretty e))

instance Pretty TVar where
  pretty (TV v k) = pretty v

instance Pretty TCon where
  pretty (TC v k) = pretty v

instance Pretty Ty where
  pretty = \case
    TVar v -> pretty v
    TCon c -> pretty c
    TGen i -> pretty $ letters !! i
    TAp (TAp (TCon (TC "(->)" _)) t1) t2 -> wrap nested t1 <+> pretty "->" <+> pretty t2
    TAp t1 t2 -> pretty t1 <+> pretty t2

nested :: Ty -> Bool
nested = \case
  TAp (TAp (TCon (TC "(->)" _)) _) _ -> True
  TAp t1 t2 -> nested t1 || nested t2
  _ -> False

instance Pretty Scheme where
  pretty (Forall [] t) = pretty t
  pretty (Forall vs t) = pretty "∀" <> hsep (map (pretty . snd) $ zip vs letters) <> pretty "." <+> pretty t

instance Pretty Constraint where
  pretty (t1 :~: t2) = pretty t1 <+> pretty "~" <+> pretty t2

instance Pretty InferErr where
  pretty (Unified t1 t2) = pretty "Cannot unify " <+> pretty t1 <+> pretty "with" <+> pretty t2
  pretty (Infinite v t) = pretty "Infinite type:" <+> pretty v <+> pretty "=" <+> pretty t
  pretty (UnboundVariable x) = pretty "Unbound variable:" <+> pretty x
  pretty (KindMismatch t1 t2) = pretty "Kind mismatch:" <+> pretty t1 <+> pretty t2
  pretty (Ambigious cs) = pretty "Ambigious constraints:" <+> pretty cs

instance Pretty ResolutionErr where
  pretty (ConfDef x) = pretty "Conflicting definitions for" <+> pretty x
  pretty (NotInScope x) = pretty "Not in scope:" <+> pretty x
  pretty (WCNotAllowed) = pretty "Wildcards not allowed in this context:"
  pretty (LitNotAllowed x) = pretty "Literals not allowed in this context:" <+> pretty x

instance Pretty RuntimeErr where
  pretty (MatchErr p) = pretty "Pattern match failure:" <+> pretty p
  pretty (DivByZero) = pretty "Division by zero"

instance Pretty Value where
  pretty VUnit = pretty "()"
  pretty (VInt i) = pretty i
  pretty (VChar c) = pretty c
  pretty (VCon c []) = pretty c
  pretty (VCon c args) = pretty c <+> hsep (map (wrap compoundV) args)
  pretty VClosure{} = pretty "??? can't print closure ???"

compoundV :: Value -> Bool
compoundV = \case
  VUnit -> False
  VInt _ -> False
  VChar _ -> False
  VCon _ [] -> False
  VCon _ _ -> True
  _ -> True
