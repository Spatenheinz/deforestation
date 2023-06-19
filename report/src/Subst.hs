{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Subst where

import Type
import Data.List (nub, union)

newtype Subst = Subst { subst :: [(TVar, Ty)] }
  deriving (Eq, Show, Ord, Semigroup, Monoid)

(@@) :: Subst -> Subst -> Subst
(@@) (Subst s1) (Subst s2) = Subst $ [(u, apply (Subst s1) t) | (u, t) <- s2] <> s1

(+->) :: TVar -> Ty -> Subst
(+->) a t = Subst [(a, t)]

class Substitutable a where
  apply :: Subst -> a -> a
  ftv   :: a -> [TVar]

instance Substitutable Ty where
  apply (Subst s) t@(TVar a) = maybe t id (Prelude.lookup a s)
  apply s (TAp a b) = TAp (apply s a) (apply s b)
  apply s t = t

  ftv = fvTy

instance Substitutable Scheme where
  apply s (Forall ks t) = Forall ks $ apply s t

  ftv (Forall ks t) = ftv t

instance Substitutable a => Substitutable [a] where
  apply = fmap . apply
  ftv   = nub . concatMap ftv
