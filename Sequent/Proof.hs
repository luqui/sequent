{-# LANGUAGE RankNTypes, TupleSections #-}

module Sequent.Proof 
    ( Proof(..)
    , proofCheck1
    , Checker
    , Hyp(..)
    , Goal(..)
    )
where

import Control.Applicative
import Control.Monad (guard)
import Data.Maybe (isNothing)
import Control.Arrow (second)
import Sequent.Syntax

newtype Hyp  = Hyp Label  deriving Show
newtype Goal = Goal Label deriving Show

data Proof h
    = Done

    -- discharge goal by exact match 
    --   with hypothesis
    | Exact Hyp Goal h

    -- modus ponens on a variable
    | Instance Expr (Hyp,Name) Label h

    -- witness an existential goal
    | Witness Name Expr h

    -- modus ponens to introduce a goal for a hypothesis's hypothesis
    | ModusGoal (Hyp,Hyp) Label Label h

    -- introduce the conclusions of a assumption-free hypothesis into
    -- the current goal
    | FlattenHyp Hyp [Label] h

    -- drop a hypothesis
    | DropHyp Hyp h
    deriving Show

instance Functor Proof where
    fmap f Done                  = Done
    fmap f (Exact h g p)         = Exact h g (f p)
    fmap f (Instance e hs l p)   = Instance e hs l (f p)
    fmap f (Witness n e p)       = Witness n e (f p)
    fmap f (ModusGoal hs l l' p) = ModusGoal hs l l' (f p)
    fmap f (FlattenHyp h ls p)   = FlattenHyp h ls (f p)
    fmap f (DropHyp h p)         = DropHyp h (f p)

data Program = Program

type Checker f = Clause -> Maybe (f Program)

proofCheck1 :: (Applicative f) => Proof (Checker f) -> Checker f
proofCheck1 Done (_ :- con) = do
    guard $ groupNull con
    return $ pure Program
proofCheck1 (Exact (Hyp hl) (Goal gl) ps) (hyp :- con) = do
    (g,con') <- groupExtractH con gl
    h <- groupFindH hyp hl
    guard $ g == h
    ps (hyp :- con')
proofCheck1 (Instance ax (Hyp b, n) zlabel ps) (hyp :- con) = do
    guard $ labelFree hyp zlabel
    AClause (bhyp :- bcon) <- groupFindH hyp b
    bhyp' <- groupUnVar n bhyp
    let newhyp = AClause (groupSubst n ax bhyp' :- groupSubst n ax bcon)
    ps (groupAddH zlabel newhyp hyp :- con)
proofCheck1 (Witness n e ps) (hyp :- con) = do
    con' <- groupUnVar n con
    ps (hyp :- groupSubst n e con')
proofCheck1 (ModusGoal (Hyp b, Hyp b') hlabel glabel ps) (hyp :- con) = do
    guard $ labelFree hyp hlabel
    guard $ labelFree con glabel
    AClause (bhyp :- bcon) <- groupFindH hyp b
    (bx, bhyp') <- groupExtractH bhyp b'
    let hyp' = groupAddH hlabel (AClause (bhyp' :- bcon)) hyp 
    let con' = groupAddH glabel bx con
    ps (hyp' :- con')
proofCheck1 (FlattenHyp (Hyp h) labels ps) (hyp :- con) = do
    guard $ all (labelFree hyp) labels
    AClause (hhyp :- hcon) <- groupFindH hyp h
    guard $ groupNull hhyp
    hcon' <- groupRelabel labels hcon
    ps (groupUnion hyp hcon' :- con)
proofCheck1 (DropHyp (Hyp i) ps) (hyp :- con) = do
    (h, hyp') <- groupExtractH hyp i
    ps (hyp' :- con)

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
    go (AType v t)
        = AType (substExpr n e v) (substExpr n e t)
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
substExpr n e (ApplyExpr es)
    = ApplyExpr (map (substExpr n e) es)

dismember :: (Eq a) => [(a,b)] -> a -> Maybe (b,[(a,b)])
dismember [] x' = Nothing
dismember ((x,y):xs) x'
    | x == x' = Just (y,xs)
    | otherwise = (fmap.fmap) ((x,y):) (dismember xs x')

dismember' :: (Eq a) => [a] -> a -> Maybe (a,[a])
dismember' xs x = (fmap.fmap.fmap) fst . flip dismember x . map dup $ xs 
    where
    dup x = (x,x)
