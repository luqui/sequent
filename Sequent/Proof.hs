{-# LANGUAGE RankNTypes, TupleSections, TemplateHaskell #-}

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
import Control.Monad (guard, foldM)
import Data.Maybe (isJust, isNothing)
import Control.Arrow (second)
import Sequent.Syntax
import Data.Traversable (Traversable(sequenceA))
import Data.Foldable (Foldable(foldMap))
import Data.Monoid (Monoid(..))
import Sequent.Fixpoint
import qualified Sequent.Program as Program
import Data.List (intercalate)
import Data.Derive (derive)
import Data.Derive.Functor
import Data.Derive.Foldable
import Data.Derive.Traversable

newtype Hyp  = Hyp Label  deriving (Eq,Ord)
newtype Goal = Goal Label deriving (Eq,Ord)

data Proof h
    = Done

    -- discharge goal by exact match 
    --   with hypothesis
    | Exact Hyp Goal h

    -- witness an existential goal
    | Witness Goal Expr h

    -- Instantiate an assumption
    | Flatten Hyp [Expr] [Label] h [Label] h

    -- introduce the hypotheses of a goal into the premises
    | Intro Goal [Label] h h

    -- document away a propositional oblighation
    | Document Goal [Hyp] Doc h

    -- implement in object language
    | Implement [Goal] Program.SourceCode h
    deriving Show

$(derive makeFunctor ''Proof)
$(derive makeFoldable ''Proof)
$(derive makeTraversable ''Proof)

withConstr :: Proof a -> Proof (a -> Proof a, a)
withConstr = go
    where
    go Done = Done
    go (Exact h g p) = Exact h g (Exact h g, p)
    go (Witness n e p) = Witness n e (Witness n e, p)
    go (Flatten h es ls p ls' p') = 
        Flatten h es ls  (\hole -> Flatten h es ls hole ls' p', p)    
                     ls' (\hole -> Flatten h es ls p ls' hole, p')
    go (Intro g ls p p') = 
        Intro g ls (\hole -> Intro g ls hole p', p)
                   (\hole -> Intro g ls p hole, p')
    go (Document g hs doc p) = Document g hs doc (Document g hs doc, p)
    go (Implement gs src p) = Implement gs src (Implement gs src, p)

infix 0 //
(//) :: Bool -> String -> Error ()
True  // _   = return ()
False // msg = fail msg

infix 0 <//
(<//) :: Maybe a -> String -> Error a
Just x  <// msg = return x
Nothing <// msg = fail msg

initProgram :: Clause -> Program.Program -> Program.Program
initProgram (Group vars hyps :- _) = Program.Lambda (zip hyps' hyps')
    where
    hyps' = vars ++ map fst hyps

data Context
    = Map.Map Hyp Type :- Map.Map Goal Type

proofCheck :: Context -> Proof a -> Error (Proof (Context, a))
proofCheck _            Done = Done
proofCheck (hyp :- con) (Exact hl gl proof') = do
    h <- Map.lookup hl hyp <// "No such hypothesis"
    g <- Map.lookup gl con <// "No such goal"
    h == g                  // "Terms do not match"
    let cx' = hyp :- Map.delete gl con
    return $ Exact hl gl (cx', proof')
proofCheck (hyp :- con) (Witness gl e proof') = do
    gl `Map.member` con     // "No such variable"
    let Goal label = gl
    let cx' = hyp :- (subst 0 (Map.singleton label e) <$> con)
    return $ Witness gl e (cx', proof')
proofCheck (hyp :- con) (Flatten hl es glabels proof' llabels proof'') = do
    Clause (Binder hhyp (Binder hcon ())) <- Map.lookup hl hyp <// "No such hypothesis" 
    all (`Map.notMember` hyp) hlabels                           // "Label already used in hypotheses"


clauseVars :: Clause -> [Name]
clauseVars (Clause (Binder hs _)) = [ k | (k,v) <- Map.assocs hs, isObject v ]

substClause :: [Expr] -> Clause -> (Group Type, Binder ()) -- (remaining hs, gs)
substClause es clause@(Clause (Binder hs cs)
    = (subst 0 sub hs, subst 0 sub cs)
    where
    vars = clauseVars clause
    sub = Map.fromList (zip vars es)
    

proofCheck1 :: (Applicative f) => Proof (Checker f) -> Checker f
proofCheck1 Done (_ :- con) = do
    groupNull con // "There are unproved obligations"
    (pure.pure) Program.Return
proofCheck1 (Exact (Hyp hl) (Goal gl) ps) (hyp :- con) = do
    (g,con') <- groupExtractH con gl <// "There is no such label " ++ gl
    h <- groupFindH hyp hl <// "There is no such label " ++ hl
    g == h   // "The terms do not match"
    (fmap.fmap) (Program.SetResult gl (Program.Variable hl)) (ps (hyp :- con'))
proofCheck1 (Witness n e ps) (hyp :- con) = do
    con' <- groupUnVar n con <// "There is no such variable " ++ n
    (fmap.fmap) (Program.SetResult n (Program.Variable (convP e))) (ps (hyp :- groupSubst n e con'))
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
proofCheck1 (Intro (Goal gl) hvars hlabels ps ps') (hyp :- con) = do
    (AClause (ghyp :- gcon), con') <- groupExtractH con gl <// "No such goal " ++ gl
    ghyp' <- groupRevar hvars =<< groupRelabel hlabels ghyp <// "Relabeling failed"
    let gcon' = foldr (.) id [ groupSubst k (VarExpr v) | (k,v) <- zip (groupVars ghyp) hvars ] $ gcon
    
    length (groupVars ghyp) == length hvars   // "Wrong number of variables"
    length (groupHyps ghyp) == length hlabels // "Wrong number of labels"

    all (labelFree hyp) hlabels // "One of the given labels is already used"

    let inputs = groupVars ghyp ++ map fst (groupHyps ghyp)
    let innards = hvars ++ hlabels

    let lambda = Program.Lambda (zip inputs innards)
    
    let consprog p p' = Program.SetResult gl (lambda p) p'

    (liftA2.liftA2) consprog (ps (groupUnion hyp ghyp' :- gcon')) 
                             (ps' (hyp :- con'))
proofCheck1 (Document (Goal gl) hs doc ps) (hyp :- con) = do
    (g, con') <- groupExtractH con gl <// "No such goal"
    and [ isJust (groupFindH hyp hl) | Hyp hl <- hs ] // "No such hypothesis"
    ps (hyp :- con')
proofCheck1 (Implement ns gls src ps) (hyp :- con) = do
    con' <- foldM (\c (Goal gl) -> snd <$> groupExtractH c gl) con gls
                <// "No such goal"
    fmap (Program.SourceCode (ns ++ [gl | Goal gl <- gls]) src) <$> ps (hyp :- con')

skolemize :: Label -> [Expr] -> [Name] -> [Expr]
skolemize l args vs = [ SkolemExpr l args (VarExpr v) | v <- vs ]

skolemizeGroup :: Label -> [Name] -> Group -> Group
skolemizeGroup label ps (Group vs hs) = Group [] ((map.fmap) substf hs)
    where 
    substs = [ subst v (SkolemExpr label (map VarExpr ps) (VarExpr v)) | v <- vs ]
    substf = foldr (.) id substs 
