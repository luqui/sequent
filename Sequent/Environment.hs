{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Sequent.Environment where

import qualified Sequent.Proof as Proof
import qualified Sequent.Parser as Parser
import Data.Monoid (mappend, mempty)
import Sequent.Syntax
import Sequent.Fixpoint
import Data.IORef
import Control.Applicative
import Control.Monad (forM_, when)

newtype PfLink r = PfLink (Suspension () (Proof.Proof r))

instance Functor PfLink where
    fmap f (PfLink s) = PfLink ((fmap.fmap) f s)

type Pf = Mu PfLink

data Environment = Environment {
    clause :: Clause,
    goals :: [(Clause, Pf -> Pf)]
}

type Obligations = Const [(Clause, Pf -> Pf)]


{-
type Checker f = Clause -> Maybe (f Program)
proofCheck1 :: Proof (Checker f) -> Checker f
-}


mapConst :: (b -> c) -> Const b a -> Const c a
mapConst f (Const b) = Const (f b)

proofCheck :: Pf -> Proof.Checker Obligations
proofCheck c = cata scheck c
    where
    scheck :: PfLink (Proof.Checker Obligations) -> Proof.Checker Obligations
    scheck (PfLink (Suspend ())) c = return $ Const [(c, id)]
    scheck (PfLink (Normal p)) c = (fmap.mapConst.fmap.fmap.fmap.xform) p (Proof.proofCheck1 p c)

    xform :: Proof.Proof a -> Pf -> Pf
    xform p q = Roll . PfLink . Normal $ fmap (const q) p


newtype IOEnv = IOEnv (IORef Environment)

newIOEnv :: Clause -> IO IOEnv
newIOEnv c = IOEnv <$> newIORef (Environment c [(c, id)])

display :: IOEnv -> IO ()
display (IOEnv r) = do
    env <- readIORef r
    forM_ (zip [0..] (goals env)) $ \(i,(c,_)) -> 
        putStrLn $ show i ++ ":: " ++ showClauseV c

tactic :: Proof.Proof () -> Pf
tactic = Roll . PfLink . Normal . fmap (const (Roll (PfLink (Suspend ()))))

a :: IOEnv -> Int -> Pf -> IO ()
a (IOEnv r) i pf = do
    env <- readIORef r
    let conts = goals env
    when (i < length conts) $ do 
        let pf' = snd (conts !! i) pf
        case proofCheck pf' (clause env) of
            Nothing -> fail "Tactic failed"
            Just (Const obs) -> writeIORef r (Environment (clause env) obs)
    display (IOEnv r)
