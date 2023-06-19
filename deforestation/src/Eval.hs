{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
module Eval where

import Data.Map (Map)
import qualified Data.Map.Strict as M
import AST
import Data.Functor
import Data.Foldable
import Data.List (find)
import Data.Function
import Debug.Trace

import Util

data Value
  = VInt Integer
  | VChar Char
  | VUnit
  | VClosure String Expr Env
  | VThunk Expr
  | VCon String [Value]

instance Show Value where
  show (VInt n) = show n
  show (VChar n) = show n
  show VUnit = "()"
  show (VClosure x e env) = "\\" ++ x ++ " " ++ show e ++ " " ++ show env
  show (VCon p ps) = p <> " " <> concatMap show ps

type Env = Map String Value

data RuntimeErr =
   MatchErr Value
  | DivByZero
  deriving(Show)

addCst :: Decl -> Env -> Env
addCst (TDecl (_, args) pats) env =
  M.fromList (map go pats) `M.union` env
  where
    go = \case
      t@(ConAlt nm ps) ->
        let inner = convertPat t
            lamfy = mkLam inner args
        in (nm, let Right res = eval env lamfy in res)

    convertPat = \case
      VarAlt x -> Var x
      ConAlt nm ps -> (foldl' App (Con nm) $ map convertPat ps)
      LitAlt l -> Lit l


runEval :: Decl -> Env -> Either RuntimeErr (Value, Env)
runEval (FDecl nm e) env =
  case eval env e of
   Right res -> return (res, M.insert nm res env)
   Left err -> Left err


eval :: Env -> Expr -> Either RuntimeErr Value
eval env = \case
  (Lit (LInt i))  -> return $ VInt i
  (Lit (LChar c)) -> return $ VChar c
  (Lit LUnit)     -> return $ VUnit

  (Var x) -> case M.lookup x env of
               Just v -> case v of VThunk e -> eval env e
                                   _ -> return v

  -- again only var in lambdas
  (Lam (Var x) b) -> return $ VClosure x b env

  (App f a) -> eval env f >>= \case
                VClosure x b env' ->
                   eval ((M.insert x (VThunk a) env') `M.union` env) b
                VCon nm vs -> do
                  a' <- eval env a
                  return $ VCon nm (vs ++ [a'])

  (Con nm) -> return $ VCon nm mempty

  (Prim op m n) -> do
    m' <- eval env m
    n' <- eval env n
    evalPrim op m' n'

  (Case e alts) -> do
    scrut <- eval env e
    go scrut alts
  where
    go v [] = Left $ MatchErr v
    go v ((pat, rhs):alts) =
      case match v pat of
        Nothing -> go v alts
        Just env' -> eval (env' `M.union` env) rhs

match :: Value  -> Pattern -> Maybe Env
match _ WildCard = return mempty
match (VInt i) (LitAlt (LInt i')) = if i == i' then return mempty else Nothing
match (VChar i) (LitAlt (LChar i')) = if i == i' then return mempty else Nothing
match VUnit (LitAlt LUnit) = return mempty
match v (VarAlt x) = return $ M.singleton x v
match (VCon vnm vs) (ConAlt nm ps) =
  if vnm == nm then foldl' merge (Just mempty) $ zipWith match vs ps
  else Nothing
  where merge Nothing _ = Nothing
        merge _ Nothing = Nothing
        merge (Just env) (Just env') = return $ env `M.union` env'
match _ _ = Nothing

evalPrim :: Op -> Value -> Value -> Either RuntimeErr Value
evalPrim Add (VInt m) (VInt n) = return $ VInt (m + n)
evalPrim Sub (VInt m) (VInt n) = return $ VInt (m - n)
evalPrim Mul (VInt m) (VInt n) = return $ VInt (m * n)
evalPrim Div (VInt m) (VInt 0) = Left DivByZero
evalPrim Div (VInt m) (VInt n) = return $ VInt (m `div` n)
