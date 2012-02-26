module Sequent.Syntax where

type Name = String

data VarClause = VarClause [Name] [Type] [Prop]

data Clause
    --           context  hypotheses  conclusions
    = ImplClause [Clause] [VarClause] [VarClause] 

data Type
    = Type [Expr]

data Prop
    = Prop [Expr]

data Expr
    = VarExpr Name
    | ApplyExpr [Expr]
    | PropExpr [Expr]
