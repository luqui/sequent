module Main where

import Sequent.Environment
import System.Environment

main = do
    [c] <- getArgs
    sequent c
