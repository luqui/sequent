module Sequent.Syntax where

type Name = String
type Label = Integer

data ClauseAtom
    = AVar Name
    | AType Expr Expr
    -- spaces in name represent argument positions
    -- eg. " divides ".
    | ARel Name [Expr]
    | AClause Clause
    deriving Eq

type Side = [(Label, ClauseAtom)]

data Clause
    = ImplClause Side Side
    deriving Eq

data Expr
    = VarExpr Name
    | ApplyExpr [Expr]
    deriving Eq
