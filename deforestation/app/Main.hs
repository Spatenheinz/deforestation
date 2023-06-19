{-# LANGUAGE FlexibleContexts #-}
module Main where

import Parser
import System.IO
import Control.Monad (unless)
import Type
import TyEnv
import Infer
import Deforest
import Pretty
import Eval
import AST
import Check
import Control.Monad.State
import System.Console.Repline
import System.Exit
import System.Directory
import qualified Data.Map.Strict as M
import Prettyprinter


data ReplState = ReplState
  { tyEnv :: TyEnv
  , termEnv :: Env
  , blazedEnv :: [(String, Expr)]
  }

testEnv = M.fromList []
testTy = TyEnv.empty
testBlazed = []

initReplState :: ReplState
initReplState = ReplState testTy testEnv testBlazed

type Repl a = HaskelineT (StateT ReplState IO) a

handleErr :: Pretty e => Either e a -> Repl a
handleErr (Right v) = return v
handleErr (Left e) = liftIO (mkPretty e) >> abort

evalDecl :: UncheckedDecl -> Repl ()
evalDecl udec = do
  st <- get
  dec' <- handleErr $ toChecked udec
  case dec' of
    t@TDecl{} -> do
      let tenv = tyEnv st
      let ty' = constructTyCon tenv t
      let env = termEnv st
      modify (\s -> s{ tyEnv = ty', termEnv = addCst t env})
    t@(FDecl nm e) -> do
      let tyEnv' = tyEnv st
      infered <- handleErr $ inferFDecl tyEnv' t
      liftIO $ mkPretty (MkTo (Var nm) infered)
      -- TODO make prettier
      let blazed = blaze e
      liftIO $ mkPretty blazed
      let blenv = blazedEnv st
      -- (_, env) <- replEval dec' st
      put st{ tyEnv = extend nm infered tyEnv', blazedEnv = (if isFn infered then (nm, blazed) : blenv else blenv)}
      -- put st{ termEnv = env, tyEnv = extend nm infered tyEnv'}

shell :: Repl a -> IO ()
shell ini = flip evalStateT initReplState $ evalReplOpts $ ReplOpts
            { banner           = const $ pure "λ> "
            , command          = cmd
            , options          = opts
            , prefix           = Just ':'
            , multilineCommand = Nothing
            , tabComplete      = completer
            , initialiser      = loadCmd "prelude/prelude.forest"
            , finaliser        = final
            }

final :: Repl ExitDecision
final = do
  liftIO $ putStrLn "Goodbye!"
  return Exit

cmd :: String -> Repl ()
cmd = exec True

exec :: Bool -> String -> Repl ()
exec update src = do
  st <- get
  decls <- handleErr $ parseStringDecls src
  mapM_ evalDecl decls


quit :: a -> Repl ()
quit _ = liftIO $ exitSuccess

evalCmd, printCmd, loadCmd :: String -> Repl ()

evalCmd str = do
  st <- get
  e <- replParse str
  liftIO $ mkPretty e
  handleErr $ inferExpr (tyEnv st) e
  (res, env) <- replEval (FDecl "it" e) st
  modify (\s -> s{ termEnv = env})
  liftIO $ mkPretty res

printCmd str = do
  e <- replParse str
  case e of
    Var nm -> do
      st <- get
      let env = blazedEnv st
      case Prelude.lookup nm env of
        Just e' -> liftIO $ mkPretty e'
        Nothing -> liftIO $ putStrLn "Variable not found"
    _ -> liftIO $ mkPretty e

loadCmd str = do
  fs <- handleErr $ parseFiles str
  mapM_ openLoad fs

deforestCmd str = do
  e <- replParse str
  st <- get
  let env = blazedEnv st
  liftIO $ mkPretty $ deforest (M.fromList env) e

openLoad :: Import -> Repl ()
openLoad (fname, prefix, vars) = do
  str <- liftIO $ readFile fname
  decls <- handleErr $ parseStringDecls str
  let toDefine = maybe decls (\x -> filter (flip elem x . findId) decls) vars
  mapM_ evalDecl toDefine
  where findId (UTDecl (nm,_) _) = nm
        findId (UFDecl (nm,_) _) = nm

typeCmd :: String -> Repl ()
typeCmd str = do
  st <- get
  e <- replParse str
  ty <- handleErr $ inferExpr (tyEnv st) e
  liftIO $ mkPretty (MkTo e ty)

opts :: Options (HaskelineT (StateT ReplState IO))
opts = [ ("eval", evalCmd)
       , ("print", printCmd)
       , ("load", loadCmd)
       , ("quit", quit)
       , ("type", typeCmd)
       , ("deforest", deforestCmd)
       ]

defaultMatcher :: MonadIO m => [(String, CompletionFunc m)]
defaultMatcher = [
    (":load"  , fileCompleter)
  --, (":type"  , values)
  ]

comp :: (Monad m, MonadState ReplState m) => WordCompleter m
comp n = do
  let cmds = [":type", ":load", ":eval", ":quit", ":print"]
  return $ []


completer :: CompleterStyle (StateT ReplState IO)
completer = Prefix (wordCompleter comp) defaultMatcher

replEval dec st = handleErr $ runEval dec (termEnv st)
replParse = handleErr . parseTopTerm

main :: IO ()
main = shell $ return ()
