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

expandRel :: String -> [String] -> String
expandRel ('_':ns) (s:ss) = s ++ expandRel ns ss
expandRel ('_':ns) [] = error "Relation arity too small"
expandRel (n:ns) ss = n : expandRel ns ss
expandRel [] (s:ss) = error "Relation arity too large"
expandRel [] [] = []

showClause :: Clause -> String
showClause (ImplClause hyps cons) = shyps ++ " -> " ++ scons
    where
    shyps = unwords $ map (showAtom.snd) hyps
    scons = unwords $ map (showAtom.snd) cons
