{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE FlexibleContexts #-}
module Parser where

import Control.Monad ( liftM2, void )
import           Data.Char           (isLower, isUpper)
import           Data.Function       (on)
import           Text.Parsec
import qualified Text.Parsec.Token as P
import Control.Monad.Combinators.Expr
import AST
import Data.Bool
import Data.Foldable (Foldable(foldr'))

type Parser a = Parsec String () a

parseFiles :: String -> Either String [Import]
parseFiles = apihelper parseLoad

parseLoad :: Parser [Import]
parseLoad = semiSep $ do f <- filename; inc <- incl; p <- prefix; return (f, p, inc)
  where incl = optionMaybe $ braces (many ident)
        prefix = option "" $ do reserved "as";
                                i <- ident;
                                bool (fail "Prefix must be Capitalized")
                                     (return i)
                                     (isCon i)

parseStringDecls :: String -> Either String Prog
parseStringDecls = apihelper $  declP `sepEndBy` (P.semi lexer)

apihelper p s = case parse (p <* eof) "" s of
                      Right x -> return x
                      Left e -> Left $ "parse-error:\n " <> show e

declP :: Parser UncheckedDecl
declP = do
  i <- ident
  args <- many ident
  op "="
  bool (UFDecl (i, args) <$> top_exprP)
       (UTDecl (i,args) <$> sepBy1 altP (op "|"))
       (isCon i)

consP :: Parser Pattern
consP = do
  i <- ident
  bool (fail "Constructor must be Capitalized")
       (ConAlt i <$> argsP) (isCon i)
  where
    varP = do v <- ident;
              bool (fail "var must be lowerletter")
                   (return $ VarAlt v) (not . isCon $ v)
    argsP = many (parens consP <|> varP)

isCon :: String -> Bool
isCon = isUpper . head

parseTopTerm :: String -> Either String Expr
parseTopTerm = apihelper top_exprP

style :: P.LanguageDef st
style = P.LanguageDef
  { P.commentStart = "{-"
  , P.commentEnd = "-}"
  , P.commentLine = "--"
  , P.nestedComments = True
  , P.identStart = letter
  , P.identLetter = alphaNum <|> oneOf "_'"
  , P.opStart = P.opLetter style
  , P.opLetter = oneOf ":!#$%&*+./<=>?@\\^|-~"
  , P.reservedOpNames = ["::","..","=","\\","|","<-","->","@","~","=>"]
  , P.reservedNames = [ "case", "of"
                      , "let", "in"
                      ]
  , P.caseSensitive = True
  }

-- expressions
appP, top_exprP, exprP, varConP, varP, litP, lamP,  caseP :: Parser Expr

appP = exprP >>= \x ->
  try (many1 exprP >>= \xs -> return $ foldl App x xs)
  <|> return x

top_exprP = makeExprParser appP table

table   = [
          [ binary "*" Mul, binary "/" Div ]
          , [ binary "+" Add, binary "-" Sub ]
          , [ binrel "<" Lt, binrel "<=" Leq, binrel ">" Gt, binrel ">=" Geq, binrel "==" Eq, binrel "/=" Neq]
          ]

binrel  name fun = InfixN (do { op name; return $ \e1 e2 -> Prim fun e1 e2 })
binary  name fun = InfixL (do { op name; return $ \e1 e2 -> Prim fun e1 e2 })

exprP = choice [ litP
               , lamP
               , caseP
               , varConP
               , parens top_exprP
               ]

varConP = do
  i <- ident
  return $ bool (Var i) (Con i) (isCon i)

varP = Var <$> ident

litP = Lit <$> lit

lit :: Parser Literal
lit = choice [ LInt <$> integer
             -- , try $  symbol "(" >> char '-' >> (LInt . negate) <$> integer <* symbol ")"
             , LChar <$> ticks (alphaNum <|> oneOf "_")
             , op "()" >> return LUnit
             ]

lamP = do
  op "\\"; args <- many1 varP; op "->"; body <- top_exprP; return $ go body args
  where go = foldr' Lam

-- letP = do
--   reserved "let"; bindId <- varP; op "="; bindExpr <- appP; reserved "in";
--   Let (NonRec {bindId, bindExpr}) <$> appP

caseP = do
  t0 <- between (reserved "case") (reserved "of") top_exprP
  Case t0 <$> sepBy1 alts (op "|")
  where alts = do p <- altP; op "->"; t <- top_exprP; return (p, t)

altP :: Parser Pattern
altP = (LitAlt <$> lit) <|> idaltP <|> wildcard <|> parens altP
  where
      idaltP = do i <- ident;
                  bool (return $ VarAlt i) (ConAlt i <$> many altP) (isCon i)
      wildcard = op "_" >> return WildCard



lexer = P.makeTokenParser style

ident :: Parser String
ident = P.identifier lexer

filename :: Parser String
filename = P.lexeme lexer $ many1 (alphaNum <|> oneOf "-._/~")

parens, braces, ticks :: Parser a -> Parser a

parens = P.parens lexer

braces = P.braces lexer

ticks x = (between `on` char) '\'' '\'' x <* P.whiteSpace lexer

semiSep = P.semiSep lexer

integer :: Parser Integer
integer = P.natural lexer

reserved, op, symbol :: String -> Parser ()
reserved = P.reserved lexer
op = P.reservedOp lexer
symbol a = P.symbol lexer a >> return ()
