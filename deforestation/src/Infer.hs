{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE LambdaCase #-}
module Infer where

import TyEnv
import Type
import Subst
import AST
import Util

import Control.Monad.Except
import Control.Monad.RWS
import Control.Monad.State
import Control.Monad.Reader

import qualified Data.Set as Set

import Debug.Trace

type Infer a = RWST
  TyEnv
  [Constraint]
  InferState
  (Except InferErr)
  a

newtype InferState = InferState { count :: Int }

initInfer :: InferState
initInfer = InferState { count = 0 }

data InferErr =
    Unified Ty Ty
  | Infinite TVar Ty
  | UnboundVariable String
  | KindMismatch Ty Ty
  | Ambigious [Constraint]

-- | Run the inference monad
runInfer :: TyEnv -> Infer Ty -> Either InferErr (Ty, [Constraint])
runInfer env m = runExcept $ evalRWST m env initInfer

inferFDecl :: TyEnv -> Decl -> Either InferErr Scheme
inferFDecl env (FDecl f m) = do
  (ty,cs) <- runInfer env $ do
                tv <- fresh Star
                let sc = toScheme tv
                local (extend f sc) $ infer m
  subst <- runSolve cs
  let t = apply subst ty
  return $ (quantify (ftv t) t)

constructTyCon :: TyEnv -> Decl -> TyEnv
constructTyCon tenv (TDecl (tcon, args) pats)
  | tcon `elem` keys tenv = error $ "type constructor " ++ tcon ++ " already defined"
  | otherwise =
    let tcon' = TCon $ TC tcon $ foldr (:->) Star (map (const Star) args)
        tvs = map (\x -> TV x Star) args
        tvars = map TVar tvs
        basic = foldl TAp tcon' tvars
        tenv' = extend tcon (quantify tvs basic) tenv
        pats' = TyEnv $ map (\(ConAlt nm ps) ->
                       (nm, quantify tvs $ foldr fn basic (map (patternToTy tenv') ps))) pats
    in pats' `merge` tenv

inferExpr :: TyEnv -> Expr -> Either InferErr Scheme
inferExpr env m = do
  (ty,cs) <- runInfer env (infer m)
  subst <- runSolve cs
  let t = apply subst ty
  return $ quantify (ftv t) t

tryFind :: Name -> Infer Ty
tryFind x = do
  env <- ask
  case TyEnv.lookup x env of
    Nothing -> throwError $ UnboundVariable x
    Just t -> inst t

quantify :: [TVar] -> Ty -> Scheme
quantify vs t = Forall ks (apply s t)
  where vs' = [ v | v <- ftv t, v `elem` vs ]
        ks  = fmap kind vs'
        s   = Subst $ zip vs' (map TGen [0..])


patternToTy :: TyEnv -> Pattern -> Ty
patternToTy env = \case
  LitAlt (LInt _) -> tInt
  LitAlt (LChar _) -> tChar
  LitAlt LUnit -> tUnit

  VarAlt v -> case TyEnv.lookup v env of
    Just (Forall _ t) -> t
    Nothing -> TVar $ TV v Star
  ConAlt c ps -> case TyEnv.lookup c env of
    Just (Forall _ t) -> t
    Nothing -> error $ "constructor " ++ c ++ " not found in patternToTy"

  WildCard -> error "wildcard in patternToTy"

inst :: Scheme -> Infer Ty
inst (Forall ks t) = do
  ts <- mapM fresh ks
  return $ instantiate ts t

class Instantiate a where
  instantiate :: [Ty] -> a -> a

instance Instantiate Ty where
  instantiate ts (TAp l r) = TAp (instantiate ts l) (instantiate ts r)
  instantiate ts (TGen n) = ts !! n
  instantiate _ t = t

instance Instantiate a => Instantiate [a] where
  instantiate ts = map (instantiate ts)


fresh :: Kind -> Infer Ty
fresh k = do
  s <- get
  put s { count = count s + 1 }
  return $ TVar $ TV (letters !! count s) k


infer :: Expr -> Infer Ty
infer = \case
  Lit (LInt _) -> return tInt
  Lit (LChar _) -> return tChar
  Lit LUnit -> return tUnit

  Var x -> tryFind x

  Lam x m -> do
    tv <- fresh Star
    -- for now we only allow variables in the lambda
    x' <- case x of
      (Var x) -> return x
      _ -> throwError $ UnboundVariable "lambda"
    t <- local (extend x' $ toScheme tv) $ infer m
    return $ tv `fn` t

  App m n -> do
    t1 <- infer m
    t2 <- infer n
    tv <- fresh Star
    tell [t1 :~: (t2 `fn` tv)]
    return tv

  Case m alts -> do
    tv <- fresh Star
    t <- infer m
    inferAlts alts tv t

  Con c -> tryFind c

  -- Fix m -> do
  --   t <- infer m
  --   tv <- fresh Star
  --   tell [t :~: (tv `fn` tv)]
  --   return tv

  Prim op m n -> do
    t1 <- infer m
    t2 <- infer n
    tv <- fresh Star
    let t = t1 `fn` t2 `fn` tv
    tell [t :~: (tOp op)]
    return tv

inferPat :: Pattern -> Infer (Ty, TyEnv)
inferPat = \case
  LitAlt (LInt _) -> return (tInt, mempty)
  LitAlt (LChar _) -> return (tChar, mempty)
  LitAlt LUnit -> return (tUnit, mempty)

  VarAlt v -> do
    tv <- fresh Star
    return (tv, extend v (toScheme tv) mempty)

  ConAlt c ps -> do
   (ts, envs) <- inferPats ps
   t' <- fresh Star
   t <- tryFind c
   tell [t :~: foldr fn t' ts]
   return (t', envs)

  WildCard -> do
    tv <- fresh Star
    return (tv, mempty)

inferPats :: [Pattern] -> Infer ([Ty], TyEnv)
inferPats ps = do
  x <- mapM inferPat ps
  let ts = map fst x
      envs = map snd x
  return (ts, foldr merge mempty envs)

inferAlt :: Ty -> AST.Alt -> Infer Ty
inferAlt t0 (p, m) = do
  (ts, env) <- inferPat p
  tell [t0 :~: ts]
  t' <- local (merge env) $ infer m
  return $ t'

inferAlts :: [AST.Alt] -> Ty -> Ty -> Infer Ty
inferAlts alts t t0 = do
  ts <- mapM (inferAlt t0) alts
  tell $ map (t :~:) ts
  return t



-- Constraint Solving

data Constraint = Ty :~: Ty
  deriving (Show)

instance Substitutable Constraint where
  apply s (t1 :~: t2) = apply s t1 :~: apply s t2

  ftv (t1 :~: t2) = ftv t1 <> ftv t2

type Unif = (Subst, [Constraint])

type Solver a = Except InferErr a

runSolve :: [Constraint] -> Either InferErr Subst
runSolve cs = runExcept $ solve (mempty, cs)

solve :: Unif -> Solver Subst
solve (sub, []) = return sub
solve (sub, (t1 :~: t2) : cs) = do
  sub' <- unify (apply sub t1) (apply sub t2)
  solve (sub' @@ sub, apply sub' cs)

unify :: Ty -> Ty -> Solver Subst
unify (TVar v) t = bind v t
unify t (TVar v) = bind v t
unify (TAp a b) (TAp a' b') = do
  s <- unify a a'
  s' <- unify (apply s b) (apply s b')
  return (s' @@ s)
unify t1 t2 | t1 == t2 = return mempty
            | otherwise =  throwError $ Unified t1 t2

bind :: TVar -> Ty -> Solver Subst
bind v t | t == TVar v = return mempty
         | v `elem` ftv t = throwError $ Infinite v t -- occurs check
         | kind v /= kind t = throwError $ KindMismatch (TVar v) t
         | otherwise = return $ v +-> t
