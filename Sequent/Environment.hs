module Sequent.Environment where

import Sequent.Proof
import Sequent.Syntax
import Data.IORef
import Control.Applicative
import Control.Monad (forM_, when)

data Environment = Environment {
    clause :: Clause,
    proof :: Proof ()
}

toConts :: Environment -> [(Clause, Proof () -> Environment)]
toConts env = [ (c, Environment (clause env) . cont hc) | (c, hc) <- holes ]
    where
    checked = proofCheck (clause env) (proof env)
    holes = holeConts checked

newtype IOEnv = IOEnv (IORef Environment)

newIOEnv :: Clause -> IO IOEnv
newIOEnv c = IOEnv <$>  newIORef (Environment c (Suspend ()))

display :: IOEnv -> IO ()
display (IOEnv r) = do
    env <- readIORef r
    let conts = toConts env
    forM_ (zip [0..] conts) $ \(i,(c,_)) -> 
        putStrLn $ show i ++ ": " ++ showClause c

applyTactic :: IOEnv -> Int -> Proof () -> IO ()
applyTactic (IOEnv r) i pf = do
    env <- readIORef r
    let conts = toConts env
    when (i < length conts) $ do 
        let env' = snd (conts !! i) pf
        writeIORef r env'

tactic :: IOEnv -> Int -> Proof () -> IO ()
tactic env i pf = applyTactic env i pf >> display env
