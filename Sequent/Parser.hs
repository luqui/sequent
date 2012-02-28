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

type Parser = P.Parsec String ()

parse :: Parser a -> String -> Either P.ParseError a
parse p = P.parse p "<input>" 

lex = P.makeTokenParser P.haskellDef

clauseElem :: Parser (Either Name (Maybe Label, ClauseAtom))
clauseElem = idful <|> ((Right . (Nothing,)) <$>  clauseAtom)
    where
    idful = convert <$> P.identifier lex <*> P.optionMaybe (P.symbol lex ":" *> clauseAtom)
    convert n Nothing = Left n
    convert n (Just a) = Right (Just n, a)

clauseAtom :: Parser ClauseAtom
clauseAtom = P.choice [ rel, cls ] 
    where
    rel = convert <$> P.brackets lex (P.many relAtom)
        where
        relAtom = P.choice [
                Left <$> P.identifier lex,
                Right <$> P.parens lex expr
            ]
        convert xs = ARel (map toName xs) (concatMap toArg xs)
        toName (Left i) = Just i
        toName (Right j) = Nothing
        toArg (Left i) = []
        toArg (Right j) = [j]
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

atomExpr :: Parser Expr
atomExpr = convert <$> P.identifier lex <*> P.optionMaybe (P.parens lex argList)
    where
    argList = expr `P.sepBy` P.symbol lex ","
    convert n Nothing = VarExpr n
    convert n (Just es) = SkolemExpr n es
