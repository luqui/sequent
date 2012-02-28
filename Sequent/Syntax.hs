module Sequent.Syntax where

import Data.Maybe (isNothing)
import Control.Applicative
import Control.Monad (guard)
import Data.List (intercalate)
import qualified Data.Set as Set

type Name = String
type Label = String

data ClauseAtom
    = ARel RelName [Expr]
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
    | SkolemExpr Label [Expr]
    deriving Eq

instance Show Expr where
    show = showExpr

showAtom :: ClauseAtom -> String
showAtom (ARel n xs) = showRel n (map showExpr xs)
showAtom (AClause c) = "(" ++ showClause c ++ ")"

showExpr :: Expr -> String
showExpr (VarExpr n) = n
showExpr (SkolemExpr l es) = l ++ "(" ++ intercalate "," (map showExpr es) ++ ")"

showRel :: RelName -> [String] -> String
showRel = \name args -> "[" ++ intercalate " " (atoms name args) ++ "]"
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

groupNull :: Group -> Bool
groupNull (Group [] []) = True
groupNull _ = False

groupUnVar :: Name -> Group -> Maybe Group
groupUnVar v (Group vs hs) = do
    (v', vs') <- dismember' vs v
    return $ Group vs' hs

groupExtractH :: Group -> Label -> Maybe (ClauseAtom, Group)
groupExtractH (Group vs hs) l = do
    (h, hs') <- dismember hs l
    return (h, Group vs hs')

groupFindH :: Group -> Label -> Maybe ClauseAtom
groupFindH g l = fst <$> groupExtractH g l

groupAddH :: Label -> ClauseAtom -> Group -> Group
groupAddH l h (Group vs hs) = Group vs (hs ++ [(l,h)])

groupUnion :: Group -> Group -> Group
groupUnion (Group vs hs) (Group vs' hs') = Group (vs ++ vs') (hs ++ hs') -- XXX alpha convert!

groupAddV :: Name -> Group -> Group
groupAddV n (Group vs hs) = Group (vs ++ [n]) hs

groupSubst :: Name -> Expr -> Group -> Group
groupSubst n e (Group vs hs)
    | n `elem` vs = Group vs hs
    | otherwise   = Group vs ((fmap.fmap) (subst n e) hs)

groupRelabel :: [Label] -> Group -> Maybe Group
groupRelabel labels (Group vs hs) = do
    guard $ length hs <= length labels 
    return $ Group vs (zip labels (map snd hs))


labelFree :: Group -> Label -> Bool
labelFree g l = isNothing (groupFindH g l)

subst :: Name -> Expr -> ClauseAtom -> ClauseAtom
subst n e = go
    where
    go (ARel n' es)
        -- substitute n'?  Higher order...
        = ARel n' (map (substExpr n e) es)
    go (AClause (hyp :- con)) =
        AClause (groupSubst n e hyp  :- groupSubst n e con)
        -- XXX if n is bound in hyp, our substitutions are overzealous

substExpr :: Name -> Expr -> Expr -> Expr
substExpr n e (VarExpr n')
    | n == n' = e
    | otherwise = VarExpr n'
substExpr n e (SkolemExpr l es)
    = SkolemExpr l (map (substExpr n e) es)

dismember :: (Eq a) => [(a,b)] -> a -> Maybe (b,[(a,b)])
dismember [] x' = Nothing
dismember ((x,y):xs) x'
    | x == x' = Just (y,xs)
    | otherwise = (fmap.fmap) ((x,y):) (dismember xs x')

dismember' :: (Eq a) => [a] -> a -> Maybe (a,[a])
dismember' xs x = (fmap.fmap.fmap) fst . flip dismember x . map dup $ xs 
    where
    dup x = (x,x)
