module Sequent.Syntax where

import Data.List (intercalate)

type Name = String
type Label = Integer

data ClauseAtom
    = AVar Name
    | AType Expr Expr
    -- spaces in name represent argument positions
    -- eg. " divides ".
    | ARel RelName [Expr]
    | AClause Clause
    deriving Eq

type RelName = [Maybe String]

type Side = [(Label, ClauseAtom)]

data Clause
    = ImplClause Side Side
    deriving Eq

instance Show Clause where
    show = showClause

data Expr
    = VarExpr Name
    | ApplyExpr [Expr]
    deriving Eq

instance Show Expr where
    show = showExpr True

showAtom :: ClauseAtom -> String
showAtom (AVar n) = n
showAtom (AType e t) = showExpr True e ++ ":" ++ showExpr True t
showAtom (ARel n xs) = "[" ++ expandRel n (map (showExpr True) xs) ++ "]"
showAtom (AClause c) = "(" ++ showClause c ++ ")"

showExpr :: Bool -> Expr -> String
showExpr parens (VarExpr n) = n
showExpr parens (ApplyExpr es) = p $ unwords (map (showExpr True) es)
    where
    p x | parens = "(" ++ x ++ ")"
        | otherwise = x

expandRel :: RelName -> [String] -> String
expandRel = \name args -> intercalate " " (atoms name args)
    where
    atoms (Just s:ss) as = s : atoms ss as
    atoms (Nothing:ss) (a:as) = a : atoms ss as
    atoms (Nothing:ss) [] = error "Too few arguments to relation"
    atoms [] (a:as) = error "Too many arguments to relation"
    atoms [] [] = []

showClause :: Clause -> String
showClause (ImplClause hyps cons) = shyps ++ " -> " ++ scons
    where
    shyps = unwords $ map (showAtom.snd) hyps
    scons = unwords $ map (showAtom.snd) cons
