{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module TyEnv where

import AST
import Type
import Subst

newtype TyEnv = TyEnv { tys :: [(Name, Scheme)] }
  deriving (Eq, Show, Semigroup, Monoid)

instance Substitutable TyEnv where
  apply s (TyEnv env) = TyEnv $ fmap (\(a, t) -> (a, apply s t)) env

  ftv (TyEnv env) = ftv $ fmap snd env

empty :: TyEnv
empty = TyEnv []

extend :: Name -> Scheme -> TyEnv -> TyEnv
extend x t (TyEnv tys) = TyEnv ((x, t) : tys)

remove :: Name -> TyEnv -> TyEnv
remove x (TyEnv tys) = TyEnv (filter ((/= x) . fst) tys)

lookup :: Name -> TyEnv -> Maybe Scheme
lookup x (TyEnv tys) = Prelude.lookup x tys

merge :: TyEnv -> TyEnv -> TyEnv
merge (TyEnv tys1) (TyEnv tys2) = TyEnv (tys1 ++ tys2)

-- mergeMany :: [TyEnv] -> TyEnv
-- mergeMany = foldr merge new

singleton :: Name -> Scheme -> TyEnv
singleton x t = TyEnv [(x, t)]

keys :: TyEnv -> [Name]
keys (TyEnv tys) = map fst tys

-- generalize :: TyEnv -> Ty -> Scheme
-- generalize env t = Forall as t
--   where as = Set.toList $ ftv t `Set.difference` ftv env
