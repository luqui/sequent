{-# LANGUAGE RankNTypes #-}

module Sequent.Proof where

import Control.Monad (guard)
import Data.Maybe (isNothing)
import Control.Arrow (second)
import Sequent.Syntax

newtype Hyp  = Hyp Label  deriving Show
newtype Goal = Goal Label deriving Show

data Proof h
    = Done
    
    -- indicate incomplete proof
    | Suspend h

    -- discharge goal by exact match 
    --   with hypothesis
    | Exact Goal Hyp (Proof h)

    -- modus ponens on a variable
    | Instance Expr (Hyp,Hyp) Label (Proof h)

    -- witness an existential goal
    | Witness Expr Goal (Proof h)

    -- modus ponens to introduce a goal for a hypothesis's hypothesis
    | ModusGoal (Hyp,Hyp) Label Label (Proof h)

    -- introduce the conclusions of a assumption-free hypothesis into
    -- the current goal
    | FlattenHyp Hyp [Label] (Proof h)

    -- drop a hypothesis
    | DropHyp Hyp (Proof h)
    deriving Show

instance Functor Proof where
    fmap f Done = Done
    fmap f (Suspend x) = Suspend (f x)
    fmap f (Exact g h p) = Exact g h (fmap f p)
    fmap f (Instance e hs l p) = Instance e hs l (fmap f p)
    fmap f (Witness e g p) = Witness e g (fmap f p)
    fmap f (ModusGoal hs l l' p) = ModusGoal hs l l' (fmap f p)
    fmap f (FlattenHyp h ls p) = FlattenHyp h ls (fmap f p)
    fmap f (DropHyp h p) = DropHyp h (fmap f p)

newtype HoleCont = HoleCont {
    cont :: forall h. Proof h -> Proof h
}

mCont :: (forall h. Proof h -> Proof h) -> HoleCont -> HoleCont
mCont f (HoleCont c) = HoleCont (f . c)

holeConts :: Proof h -> [(h, HoleCont)]
holeConts Done = []
holeConts (Suspend h) = [(h, HoleCont id)]
holeConts (Exact g h p) = (fmap.fmap) (mCont (Exact g h)) (holeConts p)
holeConts (Instance e hs l p) = (fmap.fmap) (mCont (Instance e hs l)) (holeConts p)
holeConts (Witness e g p) = (fmap.fmap) (mCont (Witness e g)) (holeConts p)
holeConts (ModusGoal hs l l' p) = (fmap.fmap) (mCont (ModusGoal hs l l')) (holeConts p)
holeConts (FlattenHyp h ls p) = (fmap.fmap) (mCont (FlattenHyp h ls)) (holeConts p)
holeConts (DropHyp h p) = (fmap.fmap) (mCont (DropHyp h)) (holeConts p)

proofCheck :: Clause -> Proof () -> Proof Clause
proofCheck (_ :- []) Done = Done
proofCheck c@(hyp :- con) (Exact (Goal gl) (Hyp hl) ps) = try c $ do
    (precon',g,postcon') <- dismember con gl
    let con' = reverse precon' ++ postcon'
    h <- lookup hl hyp
    guard $ g == h
    return $ Exact (Goal gl) (Hyp hl) $ proofCheck (hyp :- con') ps
proofCheck c@(hyp :- con) (Instance ax (Hyp b,Hyp b') zlabel ps) = try c $ do
    guard $ isNothing (lookup zlabel hyp)
    AClause (bhyp :- bcon) <- lookup b hyp
    (preb', bx, postb') <- dismember bhyp b'
    AVar n <- return bx
    let hyp' = map (second (subst n ax)) (preb' ++ postb')
    let con' = map (second (subst n ax)) bcon
    return $ Instance ax (Hyp b, Hyp b') zlabel $
             proofCheck ((bhyp ++ [(zlabel, AClause (hyp' :- con'))]) :- bcon) ps
proofCheck c@(hyp :- con) (Witness e (Goal g) ps) = try c $ do
    (preg, AVar n, postg) <- dismember con g
    let con' = map (second (subst n e)) (preg ++ postg)
    return $ Witness e (Goal g) $ proofCheck (hyp :- con') ps
proofCheck c@(hyp :- con) (ModusGoal (Hyp b, Hyp b') hlabel glabel ps) = try c $ do
    guard $ isNothing (lookup hlabel hyp)
    guard $ isNothing (lookup glabel con)
    AClause (bhyp :- bcon) <- lookup b hyp
    (preb', bx, postb') <- dismember bhyp b'
    let hyp' = hyp ++ [(hlabel, AClause ((preb' ++ postb') :- bcon))]
    let con' = con ++ [(glabel, bx)]
    -- TODO: bx must not have any variables bound in preb'
    return $ ModusGoal (Hyp b, Hyp b') hlabel glabel $ proofCheck (hyp' :- con') ps
proofCheck c@(hyp :- con) (FlattenHyp (Hyp h) labels ps) = try c $ do
    guard $ all (isNothing.flip lookup hyp) labels
    AClause ([] :- hcon) <- lookup h hyp
    let hyp' = hyp ++ zip labels (map snd hcon)
    return $ FlattenHyp (Hyp h) labels $ proofCheck (hyp' :- con) ps
proofCheck c@(hyp :- con) (DropHyp (Hyp i) ps) = try c $ do
    (preh, h, posth) <- dismember hyp i
    return $ DropHyp (Hyp i) $ proofCheck ((preh ++ posth) :- con) ps
proofCheck c _ = Suspend c

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

try :: a -> Maybe (Proof a) -> Proof a
try i = maybe (Suspend i) id

dismember :: (Eq a) => [(a,b)] -> a -> Maybe ([(a,b)],b,[(a,b)])
dismember [] _ = Nothing
dismember ((x,y):xs) x' 
    | x == x' = Just ([], y, xs)
    | otherwise = fmap (\(pre,b,post) -> ((x,y):pre,b,post)) (dismember xs x')
