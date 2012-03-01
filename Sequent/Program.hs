module Sequent.Program where

import qualified Data.Char as Char
import Data.List (intercalate)
import qualified Numeric

type Hyp = String
type Goal = String

data Program
    = Lambda [(Hyp,Hyp)] Program
    | Return
    | SetResult Goal Program Program
    | Variable Hyp
    | Apply Hyp 
            Program [(Goal, Hyp)]  -- map results of p1 to hyps of p2
            Program [(Hyp, Hyp)]   -- variables for p2
                    [(Goal, Hyp)]  -- map goals of p2 into our new hyps

indent :: String -> String -> String
indent by = unlines . map (by ++) . lines

quoteJS :: String -> String
quoteJS s
    | Char.isAlpha (head s) = concatMap trans s
    | otherwise = "$" ++ concatMap trans s
    where
    trans '_' = "__"
    trans '(' = "_E"
    trans ')' = "_D"
    trans ',' = "_j"
    trans '.' = "_o"
    trans x | Char.isAlphaNum x = [x]
    trans x = "_O" ++ pad 3 '0' (Numeric.showOct (Char.ord x) "")

    pad n c s = replicate (length s - n) c ++ s

toJS :: Program -> String
toJS (Lambda hypmap p) = 
    "function (_hyps) {\n" ++ indent "  " (
        "var _goals = {};\n" ++
        unlines [ "var " ++ quoteJS i ++ " = _hyps." ++ quoteJS o ++ ";" | (o,i) <- hypmap ] ++
        toJS p ++
        "return _goals;\n"
    ) ++ "}"
toJS Return = ""
toJS (SetResult g h p) =
    "_goals." ++ quoteJS g ++ " = " ++ toJS h ++ ";\n" ++
    toJS p
toJS (Variable h) = h
toJS (Apply f helper helpermap p vars goalmap) =
    "var _tmp = " ++ fapply ++ ";\n" ++
    unlines [ "var " ++ quoteJS res ++ " = _tmp." ++ quoteJS rparam | (rparam, res) <- goalmap ] ++
    toJS p
    where
    fapply = quoteJS f ++ "(_adapt(" ++ adapter helpermap ++ ", " ++ object vars ++ ", " ++ 
                  toJS (Lambda [] helper) ++ "()))"
    adapter xs = "{ " ++ intercalate ", " [ quoteJS k ++ ": '" ++ quoteJS v ++ "'" | (k,v) <- xs ] ++ " }"
    object xs = "{ " ++ intercalate ", " [ quoteJS k ++ ": " ++ quoteJS v | (k,v) <- xs ] ++ " }"
