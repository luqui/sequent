module Sequent.Proof where

import Control.Monad (guard)
import Data.Maybe (isNothing)
import Sequent.Syntax

data Hyp = Hyp Label
data Goal = Goal Label

data Proof h
    = Done
    
    -- indicate incomplete proof
    | Suspend h

    -- discharge goal by exact match 
    --   with hypothesis
    | Exact Goal Hyp (Proof h)

    -- modus ponens on a variable
    | Instance Expr (Hyp,Hyp) Label (Proof h)

    -- modus ponens to introduce a goal for a hypothesis's hypothesis
    | ModusGoal (Hyp,Hyp) Label Label (Proof h)

    -- introduce the conclusions of a assumption-free hypothesis into
    -- the current goal
    | FlattenHyp Hyp [Label] (Proof h)

    -- drop a hypothesis
    | DropHyp Hyp (Proof h)

proofCheck :: Clause -> Proof () -> Proof Clause
proofCheck (ImplClause _ []) Done = Done
proofCheck c (Suspend ()) = Suspend c
proofCheck c@(ImplClause hyp con) (Exact (Goal gl) (Hyp hl) ps) = try c $ do
    (precon',g,postcon') <- dismember con gl
    let con' = reverse precon' ++ postcon'
    h <- lookup hl hyp
    guard $ g == h
    return $ proofCheck (ImplClause hyp con') ps
proofCheck c@(ImplClause hyp con) (Instance ax (Hyp b,Hyp b') zlabel ps) = try c $ do
    guard $ isNothing (lookup zlabel hyp)
    AClause (ImplClause bhyp bcon) <- lookup b hyp
    (preb', bx, postb') <- dismember bhyp b'
    AVar n <- return bx
    let (hyp',s') = listSubster (subst n ax) postb'
    let (con',_) = listSubster s' bcon
    let hyp'' = preb' ++ hyp'
    return $ proofCheck (ImplClause (bhyp ++ [(zlabel, AClause (ImplClause hyp'' con'))]) bcon) ps
proofCheck c@(ImplClause hyp con) (ModusGoal (Hyp b, Hyp b') hlabel glabel ps) = try c $ do
    guard $ isNothing (lookup hlabel hyp)
    guard $ isNothing (lookup glabel con)
    AClause (ImplClause bhyp bcon) <- lookup b hyp
    (preb', bx, postb') <- dismember bhyp b'
    let hyp' = hyp ++ [(hlabel, AClause (ImplClause (preb' ++ postb') bcon))]
    let con' = con ++ [(glabel, bx)]
    -- TODO: bx must not have any variables bound in preb'
    return $ proofCheck (ImplClause hyp' con') ps
proofCheck c@(ImplClause hyp con) (FlattenHyp (Hyp h) labels ps) = try c $ do
    guard $ all (isNothing.flip lookup hyp) labels
    AClause (ImplClause [] hcon) <- lookup h hyp
    let hyp' = hyp ++ zip labels (map snd hcon)
    return $ proofCheck (ImplClause hyp' con) ps
proofCheck c@(ImplClause hyp con) (DropHyp (Hyp h) ps) = try c $ do
    (preh, h, posth) <- dismember hyp h
    return $ proofCheck (ImplClause (preh ++ posth) con) ps

newtype Subster a = Subster {
    unSubster :: a -> (a, Subster a)
}

idSubster :: Subster a
idSubster = Subster $ \a -> (a, idSubster)

listSubster :: Subster a -> [a] -> ([a], Subster a)
listSubster s [] = ([], s)
listSubster (Subster f) (c:cs) = 
    let (c',s') = f c 
        (cs',s'') = listSubster s' cs in
    (c':cs', s'')

subst :: Name -> Expr -> Subster (Label,ClauseAtom)
subst n e = Subster go
    where
    go (l,AVar n') -- TODO free var capture
        | n' == n = ((l,AVar n'), idSubster)
        | otherwise = ((l,AVar n'), subst n e)
    go (l,AType v t)
        = ((l,AType (substExpr n e v) (substExpr n e t)), subst n e)
    go (l,ARel n' es)
        -- substitute n'?  Higher order...
        = ((l,ARel n' (map (substExpr n e) es)), subst n e)
    go (l,AClause (ImplClause hyp con)) =
        let (hyp', s') = listSubster (subst n e) hyp
            (con', _) = listSubster s' con
        in 
            ((l, AClause (ImplClause hyp' con')), subst n e)

substExpr :: Name -> Expr -> Expr -> Expr
substExpr n e (VarExpr n')
    | n == n' = e
    | otherwise = VarExpr n'
substExpr n e (ApplyExpr es)
    = ApplyExpr (map (substExpr n e) es)

try :: a -> Maybe (Proof a) -> Proof a
try i = maybe (Suspend i) id

dismember :: (Eq a) => [(a,b)] -> a -> Maybe ([(a,b)],b,[(a,b)])
dismember [] _ = Nothing
dismember ((x,y):xs) x' 
    | x == x' = Just ([], y, xs)
    | otherwise = fmap (\(pre,b,post) -> ((x,y):pre,b,post)) (dismember xs x')
