module Sequent.Program where

import qualified Data.Char as Char
import Data.List (intercalate)

type Hyp = String
type Goal = String

data Program
    = Init [Hyp] Program
    | Return
    | SetResult Goal Hyp Program
    | Apply Hyp 
            Program [(Goal, Hyp)]  -- map results of p1 to hyps of p2
            Program [(Hyp, Hyp)]   -- variables for p2
                    [(Goal, Hyp)]  -- map goals of p2 into our new hyps

quoteJS :: String -> String
quoteJS = ("__" ++) . concatMap trans
    where
    trans '_' = "__"
    trans '(' = "_E"
    trans ')' = "_D"
    trans ',' = "_I"
    trans '.' = "_o"
    trans x = [x]

toJS :: Program -> String
toJS (Init hyps p) = 
    "function (_hyps) {\n" ++
    "var _goals = {};\n" ++
    unlines [ "var " ++ quoteJS h ++ " = _hyps." ++ quoteJS h ++ ";" | h <- hyps ] ++
    toJS p
toJS Return =
    "return _goals;\n" ++
    "}"
toJS (SetResult g h p) =
    "_goals." ++ quoteJS g ++ " = " ++ quoteJS h ++ ";" ++
    toJS p
toJS (Apply f helper helpermap p vars goalmap) =
    "var _tmp = " ++ fapply ++ ";\n" ++
    unlines [ "var " ++ quoteJS res ++ " = _tmp." ++ quoteJS rparam | (rparam, res) <- goalmap ] ++
    toJS p
    where
    fapply = 
        quoteJS f ++ "(_adapt(" ++ toJS (Init [] helper) ++ "(), " 
                  ++ adapter helpermap ++ ", "
                  ++ object vars ++ "))"
    adapter xs = "{ " ++ intercalate ", " [ quoteJS k ++ ": '" ++ quoteJS v ++ "'" | (k,v) <- xs ] ++ " }"
    object xs = "{ " ++ intercalate ", " [ quoteJS k ++ ": " ++ quoteJS v | (k,v) <- xs ] ++ " }"
