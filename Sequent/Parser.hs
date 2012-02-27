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

clauseAtom :: Parser ClauseAtom
clauseAtom = P.choice [
    typ,
    rel,
    cls ] 
    where
    typ = AType <$> atomExpr <* P.symbol lex ":" <*> expr
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
    cls = AClause <$> P.braces lex clause

group :: Parser Group
group = engroup <$> P.many atom
    where
    atom = P.choice [
        Left <$> P.identifier lex,
        Right <$> clauseAtom ]
    engroup xs = 
        let (vs,hs) = partitionEithers xs in
        Group vs (zipWith label [0..] hs)
    label n h = ("H" ++ show n, h)

clause :: Parser Clause
clause = (:-) <$> group <* P.symbol lex "->" <*> group

expr :: Parser Expr
expr = atomExpr

atomExpr :: Parser Expr
atomExpr = P.choice [
        VarExpr <$> P.identifier lex,
        ApplyExpr <$> P.parens lex (P.many1 atomExpr)
    ]

