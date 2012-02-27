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
    var,
    typ,
    rel ]
    where
    var = AVar <$> P.identifier lex
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

clause :: Parser Clause
clause = convert <$> P.many clauseAtom <* P.symbol lex "->" <*> P.many clauseAtom
    where
    convert hyps cons = ImplClause (zip [0..] hyps) (zip [0..] cons)

expr :: Parser Expr
expr = atomExpr

atomExpr :: Parser Expr
atomExpr = P.choice [
        VarExpr <$> P.identifier lex,
        ApplyExpr <$> P.parens lex (P.many1 atomExpr)
    ]

