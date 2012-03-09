{-# LANGUAGE TupleSections #-}

module Sequent.Parser where

import Prelude hiding (lex)
import Control.Applicative
import Data.Either (partitionEithers)
import Data.List (intercalate)
import qualified Text.Parsec as P
import qualified Text.Parsec.Token as P
import qualified Text.Parsec.Language as P
import Sequent.Syntax
import Control.Monad.Error

type Parser = P.Parsec String ()

parse :: Parser a -> String -> Either P.ParseError a
parse p = P.parse p "<input>" 

lex = P.makeTokenParser P.haskellDef { P.reservedNames = [] }

clauseElem :: Parser (Either Name (Maybe Label, ClauseAtom))
clauseElem = idful <|> ((Right . (Nothing,)) <$>  clauseAtom)
    where
    idful = convert <$> P.identifier lex <*> P.optionMaybe (P.symbol lex ":" *> clauseAtom)
    convert n Nothing = Left n
    convert n (Just a) = Right (Just n, a)

clauseAtom :: Parser ClauseAtom
clauseAtom = P.choice [ rel, cls ] 
    where
    rel = ADoc <$> P.brackets lex doc
    cls = AClause <$> P.parens lex clause

group :: Parser Group
group = engroup <$> P.many clauseElem
    where
    engroup xs = 
        let (vs,hs) = partitionEithers xs in
        Group vs (zipWith label [0..] hs)
    label n (Nothing, h) = ("H" ++ show n, h)
    label n (Just l, h) = (l, h)

clause :: Parser Clause
clause = (:-) <$> group <* P.symbol lex "->" <*> group

expr :: Parser Expr
expr = atomExpr

doc :: Parser Doc
doc = Doc <$> P.many docPart
    where
    docPart = Left <$> word <|> Right <$> qexpr
    word = P.lexeme lex (P.many1 (P.noneOf "[] \t\n'"))
    qexpr = P.char '\'' *> expr

atomExpr :: Parser Expr
atomExpr = convert <$> P.identifier lex <*> P.many skolemGroup
    where
    skolemGroup = (,) <$> P.parens lex (expr `P.sepBy` P.symbol lex ",") <*> P.optionMaybe (P.symbol lex "." *> P.identifier lex)
    convert v [] = VarExpr v
    convert v ((es, newvar):sks) = SkolemExpr v es (convert (maybe v id newvar) sks)
