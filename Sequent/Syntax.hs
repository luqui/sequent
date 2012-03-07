module Sequent.Syntax where

import Data.Maybe (isNothing)
import Control.Applicative
import Control.Monad (guard)
import Data.List (intercalate)
import qualified Data.Set as Set
import qualified Text.PrettyPrint as PP

type Name = String
type Label = String

data ClauseAtom
    = AProp Expr
    | AEq Expr Expr
    | AClause Clause
    deriving Eq

data Group = Group {
        groupVars :: [Name],
        groupHyps :: [(Label, ClauseAtom)]
    }
    deriving Eq

data Clause
    = Group :- Group
    deriving Eq

instance Show Clause where
    show = render1 . showClause

data Expr
    = VarExpr Name
    | SkolemExpr Label [Expr] Expr
    deriving Eq

instance Show Expr where
    show = render1 . showExpr

render1 = PP.renderStyle (PP.style { PP.mode=PP.OneLineMode }) 

showAtom :: ClauseAtom -> PP.Doc
showAtom (AProp p) = PP.brackets (showExpr p)
showAtom (AEq e e') = PP.brackets (showExpr e PP.<+> PP.text "=" PP.<+> showExpr e')
showAtom (AClause c) = PP.parens (showClause c)

showExpr :: Expr -> PP.Doc
showExpr (VarExpr n) = PP.text n
showExpr sk@(SkolemExpr l es v) = PP.text l PP.<> showSkolem l sk
    where
    showSkolem cx (VarExpr n)
        | n == cx = PP.empty
        | otherwise = PP.text "." PP.<> PP.text n
    showSkolem cx (SkolemExpr l es v)
        | l == cx = args PP.<> showSkolem cx v
        | otherwise = PP.hcat [PP.text ".", PP.text l, args, showSkolem l v]
        where
        args = PP.parens . PP.hcat . PP.punctuate (PP.text ",") . map showExpr $ es

showClause :: Clause -> PP.Doc
showClause (hyps :- cons) = PP.sep [showg hyps, PP.text "->", showg cons]
    where
    showg (Group vs hs) = PP.sep (PP.fsep (map PP.text vs) : map (showAtom.snd) hs)

showClauseV :: Clause -> PP.Doc
showClauseV (hyps :- cons) = PP.vcat [showg hyps, PP.text "->", showg cons]
    where
    showg (Group vs hs) = PP.vcat (PP.fsep (map PP.text vs) : map labAtom hs)
    labAtom (l,a) = PP.text l PP.<> PP.text ":" PP.<+> showAtom a

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

groupRevar :: [Name] -> Group -> Maybe Group
groupRevar names (Group vs hs) = 
    -- XXX bug!  Consider what happens if you rename [x,y] to [y,x]
    Just . Group names $ (map.fmap) (foldr (.) id [ subst v (VarExpr n) | (v,n) <- zip vs names ]) hs


labelFree :: Group -> Label -> Bool
labelFree g l = isNothing (groupFindH g l)

subst :: Name -> Expr -> ClauseAtom -> ClauseAtom
subst n e = go
    where
    go (AProp p) = AProp (substExpr n e p)
    go (AEq t t') = AEq (substExpr n e t) (substExpr n e t')
    go (AClause (hyp :- con)) =
        AClause (groupSubst n e hyp  :- groupSubst n e con)
        -- XXX if n is bound in hyp, our substitutions are overzealous

substExpr :: Name -> Expr -> Expr -> Expr
substExpr n e (VarExpr n')
    | n == n' = e
    | otherwise = VarExpr n'
substExpr n e (SkolemExpr l es v) 
    = substSkolem (SkolemExpr l es v)
    where
    substSkolem (VarExpr n) = VarExpr n
    substSkolem (SkolemExpr l es v) = SkolemExpr l (map (substExpr n e) es) (substSkolem v)

leibnizExpr :: Expr -> Expr -> Expr -> Expr
leibnizExpr from to e | e == from = to
leibnizExpr from to (VarExpr n) = VarExpr n
leibnizExpr from to (SkolemExpr l es v) = SkolemExpr l (map (leibnizExpr from to) es) (leibnizExpr from to v)

leibnizGroup :: Expr -> Expr -> Group -> Group
leibnizGroup from to (Group vars hyps) = Group vars ((fmap.fmap) (leibniz from to) hyps)
    -- XXX what if from/to have free vars occuring in vars?

leibniz :: Expr -> Expr -> ClauseAtom -> ClauseAtom
leibniz from to (AProp e) = AProp (leibnizExpr from to e)
leibniz from to (AEq e e') = AEq (leibnizExpr from to e) (leibnizExpr from to e')
leibniz from to (AClause (hyp :- con)) = AClause (leibnizGroup from to hyp :- leibnizGroup from to con)

dismember :: (Eq a) => [(a,b)] -> a -> Maybe (b,[(a,b)])
dismember [] x' = Nothing
dismember ((x,y):xs) x'
    | x == x' = Just (y,xs)
    | otherwise = (fmap.fmap) ((x,y):) (dismember xs x')

dismember' :: (Eq a) => [a] -> a -> Maybe (a,[a])
dismember' xs x = (fmap.fmap.fmap) fst . flip dismember x . map dup $ xs 
    where
    dup x = (x,x)
