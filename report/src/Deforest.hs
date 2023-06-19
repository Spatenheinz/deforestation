{-# LANGUAGE LambdaCase #-}
module Deforest where

import Util
import AST
import qualified Data.Map as M
import Data.Foldable (foldl')
import Debug.Trace
import Data.List (nub)
import Control.Monad.RWS

import Pretty

blaze :: Expr -> Expr
blaze = \case
  Lam x e ->
    let x' = getVar x
    in if linear x' e
       then Lam x (blaze e)
       else Lam (Blazed x) $ blaze e

  e@(App e1 e2) ->
    let flat = flatten e
        (hd, tl) = (head flat, tail flat)
    in case hd of
      Con _ -> toTree $ map blaze flat
      _ -> toTree $ (blaze hd) : map (\x -> if compound x then Blazed $ blaze x else x) tl

  Case e alts ->
    let scrut = if compound e then Blazed e else e
        as = map (\(pat, alt) ->
                (subst pat $ M.mapWithKey (\k _ -> linear k alt) $ binders pat,
                 blaze alt)) alts
    in Case scrut as
    where
       subst (VarAlt x) env = case M.lookup x env of
                                Just False -> PBlazed $ VarAlt x
                                Just True -> VarAlt x
       subst (ConAlt c xs) env = ConAlt c $ map (\x -> subst x env) xs
       subst x env = x

  e@(Prim op e1 e2) ->
    let e1' = if compound e1 then Blazed e1 else e1
        e2' = if compound e2 then Blazed e2 else e2
    in Blazed $ Prim op e1' e2'
  -- do nothing to var, lit, con and already blazed
  x -> x


linear :: String -> Expr -> Bool
linear x e = case M.lookup x (freeVarsOcc e) of
               Just x -> not (x > 1)
               _ -> True


blaze_ :: Expr -> Expr
blaze_ = \case
  Blazed e -> Blazed $ e
  e -> Blazed $ e


type ForestEnv = M.Map String Expr

type ForestM = RWS ForestEnv [(Var, Expr)] Int

deforest :: ForestEnv -> Expr -> Expr
deforest env e =
  let (a,w) = evalRWS (deforest' e) env 0
  in trace (unlines $ map (\(nm, e) -> nm ++ " :: " ++ debug e) w) a

lit2Var :: Expr -> Expr
lit2Var = \case
  Lit (LInt i) -> Var $ "#" <> show i
  Lit (LChar c) -> Var $ "#$" <> show c
  Lit (LUnit) -> Var $ "#()"
  e -> e

literate :: Expr -> Expr
literate = \case
  Lit i -> lit2Var $ Lit i
  Lam x e -> Lam x $ literate e
  App e1 e2 -> App (literate e1) (literate e2)
  Case e alts -> Case (literate e) (map (\(pat, alt) -> (literate_pat pat, literate alt)) alts)
  Prim op e1 e2 -> Prim op (literate e1) (literate e2)
  Blazed e -> Blazed $ literate e
  e -> e

literate_pat :: Pattern -> Pattern
literate_pat = \case
  LitAlt (LInt i) -> VarAlt $ "#" <> show i
  LitAlt (LChar c) -> VarAlt $ "#$" <> show c
  LitAlt (LUnit) -> VarAlt $ "#()"
  VarAlt x -> VarAlt x
  ConAlt c xs -> ConAlt c $ map literate_pat xs
  PBlazed p -> PBlazed $ literate_pat p

deforest' :: Expr -> ForestM Expr
deforest' = \case
  Blazed e -> blaze_ <$> deforest' e

  Var x -> return $ Var x -- $ do env <- ask
              -- case M.lookup x env of
              --   Just e -> deforest' e
              --   _ -> return $ Var x
  Lit l -> return $ lit2Var $ Lit l
  Con c -> return $ Con c

  Prim op e1 e2 -> do
    e1' <- deforest' e1
    e2' <- deforest' e2
    return $ Prim op e1' e2'

  Lam x e -> Lam x <$> deforest' e

  e@(App e1 e2) ->
    let flat = flatten e
        (hd, tl) = (head flat, tail flat)
    in case hd of
      -- rule 3
      Con c -> do
        ls <- trace("rule3") $ mapM (\x -> blaze_ <$> deforest' x) tl
        return $ toTree (hd:ls)

      Var x -> do env <- ask
                  case M.lookup x env of
                    -- rule2
                    Nothing -> do
                      ls <- trace("rule 2") $ mapM (\x -> blaze_ <$> deforest' x) tl
                      return $ toTree (hd:ls)
                    -- rule4
                    Just e' -> do
                      fvs <- fvforest e
                      trace "rule 4" $ handleF fvs x x e (toTree $ e' : tl)
      -- rule 5b
      Lam (Blazed x') e0 -> do
        let x = getVar x'
        -- let l' = Lam (Blazed . Var )
        let (e1, es) = (head tl, tail tl)
        lam <- trace "rule 5b" $ Lam (Blazed (Var x)) <$> (deforest' $ toTree $ e0 : es)
        App lam <$> (blaze_ <$> deforest' e1)

      Lam x' e0 ->
        let x = getVar x'
            (e1, es) = (head tl, tail tl)
        in case e1 of
          -- rule 5a
          Blazed e1 -> do
            lam <- trace "rule 5a" $ Lam (Var x) <$> (deforest' . toTree $ e0 : es)
            App lam <$> (blaze_ <$> deforest' e1)
          -- rule 5c (n /= 0)
          _ -> do
               let e1' = lit2Var e1
               let sub = subst x e1' e0
               trace ("rule 5c: " ++ debug e ++ "\n\n" ++ debug sub) $ deforest'  . toTree $ sub : es

  -- rule 6
  e@(Case (Blazed e0) alts) -> do
    e0' <- trace ("rule 6") $ blaze_ <$> deforest' e0
    as <- mapM (\(pat, e') -> deforest' e' >>= \x -> return (pat, x)) alts
    return $ Case e0' as

  -- rules 7-11
  e@(Case e0 alts) ->
    let e0' = flatten e0
        (hd, case_es) = (head e0', tail e0')
    in case hd of
      -- rule 8
      Con c -> do
        case matchCon c case_es alts of
          Just e' -> trace ("rule 8 " ++ debug e ++ "\n" ++ show case_es ++ "\n" ++ debug e') $ deforest' . toTree $ e' : case_es


      Var x -> do env <- ask
                  case M.lookup x env of
                    -- rule 7
                    Nothing -> trace "rule 7" $ deforest'  . blaze_ $ e0

                    -- rule 9
                    Just e' -> do
                      fvs <- fvforest e
                      trace "rule 9" $ handleF fvs x x e (Case (toTree (e' : case_es)) alts)
      -- rule 10b
      Lam (Blazed x') e0 -> do
        let x = getVar x'
        let (e1, es) = (head case_es, tail case_es)
        let case' = Case (toTree $ e0 : es) alts -- tail is is e2..en
        lam <- trace "rule 10b" $ Lam (Blazed (Var x)) <$> deforest' case'
        App lam  <$> (blaze_ <$> deforest' e1)

      Lam x' e0 ->
        let x = getVar x'
            (e1, es) = (head case_es, tail case_es)
        in case e1 of
          -- rule 10a
          Blazed e1 -> do
            let case' = Case (toTree $ e0 : es) alts
            lam <- trace "rule 10a" $ Lam (Var x) <$> deforest'  case'
            App lam <$> (blaze_ <$> deforest' e1)

          -- rule 10c
          _ -> trace "rule 10c" $ deforest' $ Case (toTree $ subst x e1 e0 : es) alts

      -- rule 11
      Case e0 alts' -> do
        let outer_e = map (\(p, e) -> (p, Case e alts)) alts'
        trace ("rule 11 " ++ debug e ++ "\n" ++ debug (Case e0 outer_e))  $ deforest' $ Case e0 outer_e



subst :: String -> Expr -> Expr -> Expr
subst x m = \case
  Var y -> if x == y then m else Var y
  Prim op e1 e2 -> Prim op (subst x m e1) (subst x m e2)
  Lam y e -> let y' = getVar y
             in if y' == x then Lam y e
                else if y' `elem` (fvs m) then
                  let banlist = fvs m <> allVars e
                  in subst x m $ rename (fresh' banlist y') $ Lam y e
             else Lam y $ subst x m e
  App e1 e2 -> App (subst x m e1) (subst x m e2)
  Case e alts ->
    let binds = map (binders . fst) alts
        subs' = map (\(binds, (p, e')) -> if M.member x binds then (p, e') else
                                     (p, subst x m e')) $ zip binds alts
    in Case (subst x m e) subs'
  Blazed e -> Blazed $ subst x m e
  e -> e

rename :: String -> Expr -> Expr
rename x (Lam y e) = let y' = getVar y in Lam (Var x) $ subst y' (Var x) e

basicname :: String -> String
basicname ('#':xs) = basicname xs
basicname xs = xs

fvforest :: Expr -> ForestM [Var]
fvforest e = do env <- ask
                let (fvs, fs) = go e
                -- return $ filter (\x -> M.notMember x env && x `notElem` fs) $ nub fvs
                return $ filter (\x -> M.notMember x env) $ nub fvs
  where
    go :: Expr -> ([Var], [Var])
    go = \case
       Blazed e -> go e
       Var x -> ([x], [])
       Lit (LInt i) -> (["#" ++ show i], [])
       Lit (LChar c) -> (["#$" ++ show c], [])
       Lit LUnit -> (["#()"], [])
       Con _ -> ([], [])
       Prim _ e1 e2 ->
         let (e1', f1s) = go e1
             (e2', f2s) = go e2
          in (e1' <> e2', f1s <> f2s)
       Lam x e -> let x'= getVar x in let (e', fs) = go e in (filter (/=x') e', fs)
       App e1 e2 -> case getVarSafe e1 of
                      Just v -> let (e', fs) = go e2 in (e', v:fs)
                      Nothing ->
                        let (e1', f1s) = go e1
                            (e2', f2s) = go e2
                        in (e1' <> e2', f1s <> f2s)
       Case e alts ->
         let (e', fvs) = go e
             (es', fs) = foldr1 (\(e1, f1) (e2, f2) -> (e1 <> e2, f1 <> f2)) $ map (\(p, e) ->
                          let (fvs, fs) = go e
                          in (filter (`notElem` M.keys (binders p)) fvs, fs)) alts
         in (e' <> es', fvs <> fs)

getLambdas :: Expr -> Int -> ([Var], Expr)
getLambdas e 0 = ([], e)
getLambdas (Lam x e) n = let x' = getVar x
                             (xs, e') = getLambdas e (n-1)
                         in (x':xs, e')
getLambdas e _ = ([], e)

-- fvs are the free variables in the expression to deforest
-- f is the original function name
-- f_cur is the current name
-- e is the original definition
-- e' is the e for f
handleF :: [Var] -> Var -> Var -> Expr -> Expr -> ForestM Expr
handleF fvs f f_cur' e e' = do
  let f_cur = "#" <> f_cur'
  env <- ask
  case M.lookup f_cur env of
    Just e'' -> do
      let (fvs',inner_e) = getLambdas e'' $ length fvs
      let e_check = foldr (\(v',v) acc -> subst v (Var v) acc) inner_e $ zip fvs' fvs
      if e == e_check then
        trace ("wtf" ++ debug e) $ return $ toTree $ (Var f_cur) : map Var fvs
      else do
        trace ("damn") $ handleF fvs f f_cur e e'
    _ -> do
      modify (+1)
      st <- get
      if st > 10 then trace "error" $ return $ Lit LUnit
      else do
        let f' = mkLam e fvs
        e'' <- trace(f_cur ++ debug e' ++ "\n" ++ debug f') $ local (M.insert f_cur f') (deforest' $ e')
        let f'' = mkLam e'' fvs
        trace ("huh?" ++ debug e'') $ tell [(f_cur, f'')]
        return $ toTree (Var f_cur : map Var fvs)

matchCon :: Name -> [Expr] -> [AST.Alt] -> Maybe Expr
matchCon c es [] = error $ "matchCon: " ++ show c ++ " " ++ show es
matchCon c es ((pi, ei):alts) =
    case matchF (Con c) es pi of
      Nothing -> matchCon c es alts
      Just env ->
        let vs = M.keys env
            lam = mkLam ei vs
        in trace ("matcon" ++ debug pi ++ show vs) $ return lam

matchF :: Expr -> [Expr] -> Pattern -> Maybe (M.Map Name Expr)
matchF _ _ WildCard = return mempty
matchF (Lit (LInt i)) _ (LitAlt (LInt i')) | i == i' = return mempty
matchF (Lit (LChar c)) _ (LitAlt (LChar c')) | c == c' = return mempty
matchF (Lit LUnit) _ (LitAlt LUnit) = return mempty
matchF v es (PBlazed e) = matchF v es e
matchF v [] (VarAlt x) = return $ M.singleton x v
matchF (Con c) es (ConAlt c' ps) =
  if c == c' then foldl' merge (Just mempty) $ zipWith (\x y -> matchF x [] y) es ps
  else Nothing
  where merge Nothing _ = Nothing
        merge _ Nothing = Nothing
        merge (Just env) (Just env') = return $ env `M.union` env'
matchF _ _ _ = Nothing
