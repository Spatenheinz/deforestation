{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE LambdaCase #-}
module Type where

import AST
import Data.List (nub, union)
import Util

data TVar = TV String Kind
  deriving (Eq, Ord, Show)

data TCon = TC String Kind
  deriving (Eq, Ord, Show)

data Kind = Star
  | Kind :-> Kind
  deriving (Eq, Ord, Show)

infixr 4 :->

data Ty
  = TVar TVar
  | TCon TCon
  | TAp Ty Ty
  | TGen Int
  deriving (Eq, Ord, Show)

infixr      4 `fn`
fn         :: Ty -> Ty -> Ty
a `fn` b    = TAp (TAp tArrow a) b

data Scheme = Forall [Kind] Ty
  deriving (Eq, Ord, Show)

toScheme :: Ty -> Scheme
toScheme t = Forall [] t

fvTy :: Ty -> [TVar]
fvTy (TVar a)   = [a]
fvTy (TAp t s)  = fvTy t `union` fvTy s
fvTy _ = mempty

tInt, tChar, tUnit, tList, tArrow :: Ty
tInt  = TCon $ TC "Int" Star
tChar = TCon $ TC "Char" Star
tUnit = TCon $ TC "()" Star
tList = TCon $ TC "[]" (Star :-> Star)
tBool = TCon $ TC "Bool" Star
tArrow = TCon $ TC "(->)" (Star :-> Star :-> Star)

class IsFn t where
  isFn :: t -> Bool

instance IsFn Ty where
  isFn (TAp (TAp (TCon (TC "(->)" _)) _) _) = True
  isFn _ = False

instance IsFn Scheme where
  isFn (Forall _ t) = isFn t

tOp :: Op -> Ty
tOp Add = tInt `fn` tInt `fn` tInt
tOp Sub = tInt `fn` tInt `fn` tInt
tOp Mul = tInt `fn` tInt `fn` tInt
tOp Div = tInt `fn` tInt `fn` tInt
tOp Lt = tInt `fn` tInt `fn` tBool
tOp Gt = tInt `fn` tInt `fn` tBool
tOp Eq = tInt `fn` tInt `fn` tBool
tOp Neq = tInt `fn` tInt `fn` tBool
tOp Leq = tInt `fn` tInt `fn` tBool
tOp Geq = tInt `fn` tInt `fn` tBool

class HasKind t where
  kind :: t -> Kind

instance HasKind TVar where
  kind (TV _ k) = k

instance HasKind TCon where
  kind (TC _ k) = k

instance HasKind Ty where
  kind (TVar v)   = kind v
  kind (TCon c)   = kind c
  kind (TAp t s)  = case kind t of _ :-> k -> k; k -> error $ "kind error: " ++ show (TAp t s) ++ "kind " ++ show k
