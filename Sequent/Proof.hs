{-# LANGUAGE RankNTypes #-}

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
    | Instance Expr (Hyp,Hyp) Label h

    -- witness an existential goal
    | Witness Expr Goal h

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
    fmap f (Witness e g p)       = Witness e g (f p)
    fmap f (ModusGoal hs l l' p) = ModusGoal hs l l' (f p)
    fmap f (FlattenHyp h ls p)   = FlattenHyp h ls (f p)
    fmap f (DropHyp h p)         = DropHyp h (f p)

data Program = Program

type Checker f = Clause -> Maybe (f Program)

proofCheck1 :: (Applicative f) => Proof (Checker f) -> Checker f
proofCheck1 Done (_ :- []) = return $ pure Program
proofCheck1 (Exact (Hyp hl) (Goal gl) ps) (hyp :- con) = do
    (g,con') <- dismember con gl
    h <- lookup hl hyp
    guard $ g == h
    ps (hyp :- con')
proofCheck1 (Instance ax (Hyp b,Hyp b') zlabel ps) (hyp :- con) = do
    guard $ labelFree hyp zlabel
    AClause (bhyp :- bcon) <- lookup b hyp
    (bx, hyp') <- dismember bhyp b'
    AVar n <- return bx
    let substs = (fmap.fmap) (subst n ax)
    ps (substs hyp' :- substs con)
proofCheck1 (Witness e (Goal g) ps) (hyp :- con) = do
    (AVar n, con') <- dismember con g
    ps (hyp :- (fmap.fmap) (subst n e) con')
proofCheck1 (ModusGoal (Hyp b, Hyp b') hlabel glabel ps) (hyp :- con) = do
    guard $ labelFree hyp hlabel
    guard $ labelFree con glabel
    AClause (bhyp :- bcon) <- lookup b hyp
    (bx, bhyp') <- dismember bhyp b'
    let hyp' = hyp ++ [(hlabel, AClause (bhyp' :- bcon))]
    let con' = con ++ [(glabel, bx)]
    ps (hyp' :- con')
proofCheck1 (FlattenHyp (Hyp h) labels ps) (hyp :- con) = do
    guard $ all (labelFree hyp) labels
    AClause ([] :- hcon) <- lookup h hyp
    let hyp' = hyp ++ zip labels (map snd hcon)
    ps (hyp' :- con)
proofCheck1 (DropHyp (Hyp i) ps) (hyp :- con) = do
    (h, hyp') <- dismember hyp i
    ps (hyp' :- con)
proofCheck1 _ _ = Nothing

labelFree :: (Eq a) => [(a,b)] -> a -> Bool
labelFree xs x = isNothing (lookup x xs)

subst :: Name -> Expr -> ClauseAtom -> ClauseAtom
subst n e = go
    where
    go (AVar n') -- TODO free var capture
        | n' == n = AVar n'
        | otherwise = AVar n'
    go (AType v t)
        = AType (substExpr n e v) (substExpr n e t)
    go (ARel n' es)
        -- substitute n'?  Higher order...
        = ARel n' (map (substExpr n e) es)
    go (AClause (hyp :- con)) =
        AClause (map (second (subst n e)) hyp :- map (second (subst n e)) con)

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
