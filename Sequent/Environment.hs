{-# LANGUAGE GeneralizedNewtypeDeriving, TypeOperators, TupleSections #-}

module Sequent.Environment where

import qualified Sequent.Proof as Proof
import qualified Sequent.Parser as Parser
import qualified Text.Parsec as P
import qualified Text.Parsec.Token as P
import Data.Monoid (mappend, mempty)
import Sequent.Syntax
import Sequent.Fixpoint
import Data.IORef
import Control.Applicative
import Control.Monad (forM_, when, guard)
import Control.Monad.Identity
import qualified System.Console.Readline as Readline
import qualified Sequent.Program as Program
import qualified Text.PrettyPrint as PP

type PfLink = Suspension () :. Proof.Proof
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

embedPf :: Proof.Proof Pf -> Pf
embedPf = Roll . O . Normal 

extractProof :: Pf -> Maybe (Mu Proof.Proof)
extractProof pf =
    case sequenceMu pf of
        Suspend _ -> Nothing
        Normal x -> Just x

genProgram :: Mu Proof.Proof -> Clause -> Error Program.Program
genProgram = (fmap.fmap) runIdentity . cata Proof.proofCheck1

proofCheck :: Pf -> Proof.Checker Obligations
proofCheck c = cxCata scheck c
    where
    scheck :: PfLink (Proof.Checker Obligations, Pf) -> Proof.Checker Obligations
    scheck (O (Suspend ())) c = return $ Const [(c, id)]
    scheck (O (Normal p)) c = Proof.proofCheck1 p' c
        where
        --p :: Proof (Checker Obligations, Pf)
        --withConstr p :: Proof ((Checker,Pf) -> Proof (Checker,Pf), (Checker,Pf))

        pfConstrs :: Proof.Proof (Pf -> Pf, Proof.Checker Obligations)
        pfConstrs = fmap t (Proof.withConstr p)
            where
            t (f, (checker, _)) = (\pf' -> embedPf (fmap snd (f (checker,pf'))), checker)
        
        p' :: Proof.Proof (Proof.Checker Obligations)
        p' = fmap (\(pff, checker) -> (fmap.fmap.mapConst.fmap.fmap) (pff .) checker) pfConstrs

constructor :: Proof.Proof a -> Pf -> Pf
constructor p q = Roll . O . Normal $ fmap (const q) p

sequent :: String -> IO Environment
sequent s = do
    case Parser.parse Parser.clause s of
        Left err -> fail $ show err
        Right cl -> interactive (Environment cl [(cl, id)])

eraseDisplay = putStrLn "\27[2J"

interactive :: Environment -> IO Environment
interactive = go "" []
    where
    go msg history env = do
        eraseDisplay
        putStrLn msg
        display env
        maybeLine <- readline
        case maybeLine of
            Nothing -> return env
            Just "undo" -> do
                case history of
                    [] -> go "Nothing was done to undo" history env
                    (x:xs) -> go "" xs x
            Just line -> do
                case P.parse parseProof "<input>" line of
                    Left err -> go (show err) history env
                    Right (n,proof) -> 
                        case applyProof n (tactic proof) env of
                            Error err  -> go ("Proof error: " ++ err) history env
                            Ok (env',pf)
                                | null (goals env') -> do
                                    putStrLn "Definition complete"
                                    Just pf' <- return $ extractProof pf
                                    print pf'
                                    Ok prog <- return $ Proof.initProgram (clause env) 
                                                            <$> genProgram pf' (clause env)
                                    putStrLn "----- JS -----"
                                    putStrLn $ Program.toJS prog
                                    return env
                                | otherwise         -> go "" (env:history) env'

readline = do
    mline <- Readline.readline "> "
    case mline of
        Nothing -> return Nothing
        Just line -> Readline.addHistory line >> return (Just line)

parseProof = (,) <$> (fromIntegral <$> P.natural lex) <*> P.choice [
    "done"     --> pure (const Proof.Done),
    "exact"    --> Proof.Exact <$> hyp <*> goal,
    "witness"  --> Proof.Witness <$> var <*> expr,
    "flatten"  --> Proof.Flatten <$> hyp <*> list expr <*> list label <*> list label <*> pure (),
    "intro"    --> Proof.Intro <$> goal <*> list var <*> list label <*> pure (),
    "doc"      --> Proof.Document <$> goal <*> list hyp <*> doc
    ]
    where
    infix 0 --> 
    n --> p = P.reserved lex n *> (p <*> pure ())
    lex = Parser.lex
    label = P.identifier lex
    var = P.identifier lex
    hyp = Proof.Hyp <$> label
    goal = Proof.Goal <$> label
    expr = Parser.expr
    list p = P.parens lex $ p `P.sepBy` (P.symbol lex ",")
    doc = Parser.doc

indent :: String -> String -> String
indent by = unlines . map (by ++) . lines
 
display :: Environment -> IO ()
display env =
    putStrLn . PP.render $
        PP.vcat [ PP.text (show i ++ "::") PP.$+$ (PP.nest 2 (showClauseV c)) | (i,(c,_)) <- zip [0..] (goals env) ]

tactic :: Proof.Proof () -> Pf
tactic p = constructor p . Roll . O $ Suspend ()

applyProof :: Int -> Pf -> Environment -> Error (Environment, Pf)
applyProof i pf env = do
    let conts = goals env
    guard $ i < length conts
    let pf' = snd (conts !! i) pf
    (,pf') . Environment (clause env) . getConst <$> proofCheck pf' (clause env)
