{-# LANGUAGE LambdaCase #-}
module Check where
import AST
import Data.Map (Map)
import qualified Data.Map.Strict as Map
import Control.Monad (when, (>=>))
import Data.Foldable (foldrM, foldr', foldl')
import Data.Either (either)
import Data.Bool
import Util

data ResolutionErr = ConfDef Var
                     | NotInScope Var
                     | WCNotAllowed
                     | LitNotAllowed Var
                     deriving(Show)

type Resolve b = Either ResolutionErr b

-- Checks that none of the arguments are equivalent -
-- both at value and type level are equivalent forall
checkDeclArg :: UncheckedDecl -> Resolve UncheckedDecl
checkDeclArg utd = case utd of
                     UTDecl (_, vs) _ -> check vs
                     UFDecl (_, vs) _ -> check vs
  where check vs = foldrM checkVar [] vs >> return utd
        checkVar :: Name -> [Name] -> Resolve [Name]
        checkVar v vs = bool (Left $ ConfDef v) (return $ v:vs) (v `notElem` vs)

-- Checks that the types are in scope
checkCon :: UncheckedDecl -> Resolve UncheckedDecl
checkCon utd@(UTDecl (_, vs) pats) = checkPats pats >> return utd
  where checkPats ps = mapM (`checkPat` vs) ps
        checkPat (ConAlt _ ps) _ = checkPats ps >> return ()
        checkPat (VarAlt v) vs = bool (Left $ NotInScope v) (return ()) (v `elem` vs)
-- Dont do anything for function Declarations
checkCon x = return x

-- Check that cases patterns dont use the same name
checkCase :: UncheckedDecl -> Resolve UncheckedDecl
checkCase ufd@(UFDecl _ body) = const (return ufd) =<< check body
  where check :: Expr -> Resolve ()
        check (Lam x b) = check b
        -- check (Let x b) = check (bindExpr x) >> check b
        check (App f x) = check f >> check x
        check (Case e alts) = check e >>
                              sequence (mapM (checkPat . fst) alts []) >>
                              mapM (check . snd) alts >> return ()
        check _ = return ()
        checkPat :: Pattern -> [Var] -> Resolve [Var]
        checkPat (ConAlt _ alts) seen = foldrM checkPat seen alts
        checkPat (VarAlt v) seen = bool (Left $ ConfDef v) (return $ v:seen) (v `notElem` seen)
        checkPat _ seen = return seen
-- no case expressions in types.
checkCase x = return x

-- checkRec :: Decl -> Resolve Decl
-- checkRec fd@(TDecl nm body) = return fd
-- checkRec fd@(FDecl nm body) = return $ bool fd (FDecl nm $ Fix . Lam (Var nm) $ body) (check body nm)
--   where check (Var x) nm = x == nm
--         -- check (Let _ b) nm = check b nm
--         check (Lam _ b) nm = check b nm
--         check (App f x) nm = check f nm || check x nm
--         check (Case e alts) nm = check e nm || any (flip check nm . snd) alts
--         check (Con _) nm = False
--         check _ _ = False


desugarArgs :: UncheckedDecl -> Resolve Decl
desugarArgs (UFDecl (nm,vs) body) = return $ FDecl nm $ mkLam body vs
desugarArgs (UTDecl h cons) = return $ TDecl h cons
  -- where constructor (ConAlt c args) = FDecl c $ mkLam $ foldl' vars [] args
  --       vars (ConAlt _ args) vs = foldl' vars vs args
  --       vars (VarAlt v) vs = v:vs


toChecked :: UncheckedDecl -> Resolve Decl
toChecked = checkDeclArg >=> checkCon >=> checkCase >=> desugarArgs -- >=> checkRec
