module AST where

import Data.Map (Map)
import qualified Data.Map.Strict as M

import Debug.Trace

data Expr = Var Var -- variable
          | Lit Literal
          | Lam Expr Expr
          -- | Let Bind Expr
          | App Expr Expr
          | Case Expr [Alt]
          | Con Name
          | Prim Op Expr Expr
          | Blazed Expr
  deriving(Show, Eq)

data Op = Add | Sub | Mul | Div
      | Lt | Gt | Eq | Neq | Leq | Geq
  deriving(Eq)

instance Show Op where
  show Add = "(+)"
  show Sub = "(-)"
  show Mul = "(*)"
  show Div = "(/)"
  show Lt = "(<)"
  show Gt = "(>)"
  show Eq = "(==)"
  show Neq = "(/=)"
  show Leq = "(<=)"
  show Geq = "(>=)"

data Pattern = ConAlt Name [Pattern]   -- Constructor Pattern
             | VarAlt Var
             | LitAlt Literal    -- literals
             | WildCard              -- wildcard
             | PBlazed Pattern
  deriving(Show, Eq)

type Alt = (Pattern, Expr)

type Var = String

data Literal = LInt Integer
             | LChar Char
             | LUnit
  deriving(Show, Eq)
type Name = String

type Import = (FileName, Prefix, Maybe [Var])
type FileName = String
type Prefix = String

type TyHead = (Name, [Name])

data UncheckedDecl = UTDecl TyHead [Pattern]
                   | UFDecl TyHead Expr
  deriving(Show)

data Decl = TDecl TyHead [Pattern]
          | FDecl Name Expr
  deriving(Show, Eq)

type Prog = [UncheckedDecl]


freeVarsOcc :: Expr -> Map Var Int
freeVarsOcc (Var v) = M.singleton v 1
freeVarsOcc (Lit _) = M.empty
freeVarsOcc (Lam v e) = freeVarsOcc e `M.difference` M.singleton (getVar v) 1
freeVarsOcc (App e1 e2) = M.unionWith (+) (freeVarsOcc e1) (freeVarsOcc e2)
freeVarsOcc (Case e alts) =
  let alts' = map (\(p, e) -> M.difference (freeVarsOcc e) (binders p)) alts
      maxed = foldl (M.unionWith max) M.empty alts'
  in M.unionWith (+) (freeVarsOcc e) maxed


freeVarsOcc (Con _) = M.empty
freeVarsOcc (Prim _ e1 e2) = M.unionWith (+) (freeVarsOcc e1) (freeVarsOcc e2)
freeVarsOcc (Blazed e) = freeVarsOcc e

binders :: Pattern -> Map Var Int
binders (VarAlt x) = M.singleton x 1
binders (ConAlt _ xs) = M.unions $ map binders xs
binders (PBlazed p) = binders p
binders _ = M.empty


getVar :: Expr -> Var
getVar (Var v) = v
getVar (Blazed e) = getVar e
getVar _ = error "getVar: not a variable"

getVarSafe :: Expr -> Maybe Var
getVarSafe (Var v) = Just v
getVarSafe (Blazed e) = getVarSafe e
getVarSafe _ = Nothing

fvs :: Expr -> [Var]
fvs = M.keys . freeVarsOcc

allVars :: Expr -> [Var]
allVars e = fvs e <> bvs e

bvs :: Expr -> [Var]
bvs (Var _) = []
bvs (Lit _) = []
bvs (Lam v e) = getVar v : bvs e
bvs (App e1 e2) = bvs e1 ++ bvs e2
bvs (Case e alts) =
  let e' = bvs e
      alts' = concatMap (\(p, e) -> M.keys (binders p) ++ bvs e) alts
  in e' ++ alts'
bvs (Con _) = []
bvs (Prim _ e1 e2) = bvs e1 ++ bvs e2
bvs (Blazed e) = bvs e

fresh' :: [Var] -> Var -> Var
fresh' vs v = if v `elem` vs then fresh' vs (v ++ "'") else v
