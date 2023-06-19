{-# LANGUAGE LambdaCase #-}
module Util where

import Control.Monad (replicateM)
import AST
import Data.Foldable (foldr')

letters :: [String]
letters = [1..] >>= flip replicateM ['a'..'z']

mkLam :: Expr -> [Var] -> Expr
mkLam = foldr' (Lam . Var)

flatten :: Expr -> [Expr]
flatten expr = case expr of
  App e1 e2 -> flatten e1 ++ [e2]
  _ -> [expr]

toTree :: [Expr] -> Expr
toTree = foldl1 App

compound :: Expr -> Bool
compound = \case
  Var _ -> False
  Lit _ -> False
  Con _ -> False
  Blazed _ -> False
  _ -> True
