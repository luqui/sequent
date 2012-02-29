{-# LANGUAGE RankNTypes, TupleSections #-}

module Sequent.Proof 
    ( Proof(..)
    , proofCheck1
    , initProgram
    , Checker
    , Constructor
    , withConstr
    , Hyp(..)
    , Goal(..)
    )
where

import Control.Applicative
import Control.Monad (guard)
import Data.Maybe (isNothing)
import Control.Arrow (second)
import Sequent.Syntax
import Data.Traversable (Traversable(sequenceA))
import Data.Foldable (Foldable(foldMap))
import Data.Monoid (Monoid(..))
import Sequent.Fixpoint
import qualified Sequent.Program as Program
import Data.List (intercalate)

newtype Hyp  = Hyp Label  deriving Show
newtype Goal = Goal Label deriving Show

data Proof h
    = Done

    -- discharge goal by exact match 
    --   with hypothesis
    | Exact Hyp Goal h

    -- witness an existential goal
    | Witness Name Expr h

    -- skolemize and introduce conclusions of a hypothesis into the 
    -- current goal
    | Flatten Hyp [Expr] [Label] [Label] h h
    deriving Show

instance Functor Proof where
    fmap f Done                       = Done
    fmap f (Exact h g p)              = Exact h g (f p)
    fmap f (Witness n e p)            = Witness n e (f p)
    fmap f (Flatten h es ls ls' p p') = Flatten h es ls ls' (f p) (f p')

instance Foldable Proof where
    foldMap f Done = mempty
    foldMap f (Exact _ _ x) = f x
    foldMap f (Witness _ _ x) = f x
    foldMap f (Flatten _ _ _ _ x x') = f x `mappend` f x'

instance Traversable Proof where
    sequenceA Done = pure Done
    sequenceA (Exact h g x) = Exact h g <$> x
    sequenceA (Witness n e x) = Witness n e <$> x
    sequenceA (Flatten h es l l' x x') = Flatten h es l l' <$> x <*> x'

type Constructor a = a -> Proof a

withConstr :: Proof a -> Proof (Constructor a, a)
withConstr = go
    where
    go Done = Done
    go (Exact h g p) = Exact h g (Exact h g, p)
    go (Witness n e p) = Witness n e (Witness n e, p)
    go (Flatten h es ls l' p p') = 
        Flatten h es ls l' (\hole -> Flatten h es ls l' hole p', p)    
                           (\hole -> Flatten h es ls l' p hole, p')

type Checker f = Clause -> Error (f Program.Program)

infix 0 //
(//) :: Bool -> String -> Error ()
True  // _   = return ()
False // msg = fail msg

infix 0 <//
(<//) :: Maybe a -> String -> Error a
Just x  <// msg = return x
Nothing <// msg = fail msg

initProgram :: Clause -> Program.Program -> Program.Program
initProgram (Group vars hyps :- _) = Program.Init hyps'
    where
    hyps' = vars ++ map fst hyps

convP :: Expr -> String
convP (VarExpr n) = n
convP (SkolemExpr n es v) = 
    concat [n, "(", intercalate "," (map convP es), ").", convP v]

proofCheck1 :: (Applicative f) => Proof (Checker f) -> Checker f
proofCheck1 Done (_ :- con) = do
    groupNull con // "There are unproved obligations"
    (pure.pure) Program.Return
proofCheck1 (Exact (Hyp hl) (Goal gl) ps) (hyp :- con) = do
    (g,con') <- groupExtractH con gl <// "There is no such label " ++ gl
    h <- groupFindH hyp hl <// "There is no such label " ++ hl
    g == h   // "The terms do not match"
    (fmap.fmap) (Program.SetResult gl hl) (ps (hyp :- con'))
proofCheck1 (Witness n e ps) (hyp :- con) = do
    con' <- groupUnVar n con <// "There is no such variable " ++ n
    (fmap.fmap) (Program.SetResult n (convP e)) (ps (hyp :- groupSubst n e con'))
proofCheck1 (Flatten (Hyp h) es glabels hlabels ps ps') (hyp :- con) = do
    all (labelFree hyp) hlabels // "One of the labels is already used in the hypotheses"
    all (labelFree con) glabels // "One of the labels is already used in the goals"

    AClause (hhyp :- hcon) <- groupFindH hyp h <// "There is no such label " ++ h
    
    -- find the list of hypotheses and what they should be substituted for
    let Group hhyp_vs hhyp_hs = hhyp
    length hhyp_vs == length es // "There must be the same number of variables and instantiators"
    let substs = zip hhyp_vs es
    
    -- name the conclusions as skolem functions of the hypotheses
    -- a b -> c d  ==>   a b -> c(a,b) d(a,b)
    let Group _ hcon_hs' = skolemizeGroup h hhyp_vs hcon

    let subster h = foldr (uncurry subst) h substs
    
    -- relabel and put into main context
    premises <- groupRelabel glabels (Group [] ((map.fmap) subster hhyp_hs)) <// "Relabeling failed"
    conclusions <- groupRelabel hlabels (Group [] ((map.fmap) subster hcon_hs')) <// "Relabeling failed"

    let Group hcon_vs hcon_hs = hcon

    let goalmap = zip (map fst hcon_hs') hlabels ++
                  zip hcon_vs (map convP (skolemize h es hcon_vs))

    let consprog p p' = Program.Apply h p (zip glabels (map fst hhyp_hs))
                                        p' (zip hhyp_vs (map convP es))
                                           goalmap

    (liftA2.liftA2) consprog 
                    (ps (hyp :- premises)) (ps' (groupUnion hyp conclusions :- con))

skolemize :: Label -> [Expr] -> [Name] -> [Expr]
skolemize l args vs = [ SkolemExpr l args (VarExpr v) | v <- vs ]

skolemizeGroup :: Label -> [Name] -> Group -> Group
skolemizeGroup label ps (Group vs hs) = Group [] ((map.fmap) substf hs)
    where 
    substs = [ subst v (SkolemExpr label (map VarExpr ps) (VarExpr v)) | v <- vs ]
    substf = foldr (.) id substs 
