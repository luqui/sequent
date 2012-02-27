module Sequent.Syntax where

import Data.List (intercalate)

type Name = String
type Label = String

data ClauseAtom
    = AType Expr Expr
    | ARel RelName [Expr]
    | AClause Clause
    deriving Eq

type RelName = [Maybe String]

data Group = Group [Name] [(Label, ClauseAtom)]
    deriving Eq

data Clause
    = Group :- Group
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
showClause (hyps :- cons) = showg hyps ++ " -> " ++ showg cons
    where
    showg (Group vs hs) = unwords (vs ++ map (showAtom.snd) hs)

showClauseV :: Clause -> String
showClauseV (hyps :- cons) = showg hyps ++ "->\n" ++ showg cons
    where
    showg (Group vs hs) = unlines $ 
        mkVs vs ++ map (\(i,x) -> i ++ ": " ++ showAtom x) hs
    mkVs [] = []
    mkVs vs = [unwords vs]
