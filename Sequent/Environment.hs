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
    proof :: Pf
}

type SuspendChecker = Const [(Clause, Pf -> Pf)]


{-
type Checker f = Clause -> Maybe (f Program)
proofCheck1 :: Proof (Checker f) -> Checker f
-}


proofCheck :: Pf -> Proof.Checker SuspendChecker
proofCheck c = cata scheck c
    where
    scheck :: PfLink (Proof.Checker SuspendChecker) -> Proof.Checker SuspendChecker
    scheck (PfLink (Suspend ())) c = return $ Const [(c, id)]
    scheck (PfLink (Normal p)) c = Proof.proofCheck1 p c

{-
toConts :: Environment -> [(Clause, Proof () -> Environment)]
toConts env = [ (c, Environment (clause env) . cont hc) | (c, hc) <- holes ]
    where
    checked = proofCheck (clause env) (proof env)
    holes = holeConts checked

newtype IOEnv = IOEnv (IORef Environment)

proofIO :: IOEnv -> IO (Proof ())
proofIO (IOEnv r) = proof <$> readIORef r

newIOEnv :: Clause -> IO IOEnv
newIOEnv c = IOEnv <$>  newIORef (Environment c (Suspend ()))

display :: IOEnv -> IO ()
display (IOEnv r) = do
    env <- readIORef r
    let conts = toConts env
    forM_ (zip [0..] conts) $ \(i,(c,_)) -> 
        putStrLn $ show i ++ ":: " ++ showClauseV c

applyTactic :: IOEnv -> Int -> Proof () -> IO ()
applyTactic (IOEnv r) i pf = do
    env <- readIORef r
    let conts = toConts env
    when (i < length conts) $ do 
        let env' = snd (conts !! i) pf
        writeIORef r env'

tactic :: IOEnv -> Int -> Proof () -> IO ()
tactic env i pf = applyTactic env i pf >> display env
-}
