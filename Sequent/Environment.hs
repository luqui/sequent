{-# LANGUAGE GeneralizedNewtypeDeriving, TypeOperators #-}

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
import qualified System.Console.Readline as Readline

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

interactive :: Environment -> IO Environment
interactive = go
    where
    go env = do
        display env
        maybeLine <- readline
        case maybeLine of
            Nothing -> return env
            Just line -> do
                case P.parse parseProof "<input>" line of
                    Left err -> print err >> go env
                    Right (n,proof) -> 
                        case applyProof n (tactic proof) env of
                            Error err  -> putStrLn ("Proof error: " ++ err) >> go env
                            Ok env'
                                | null (goals env') -> do
                                    putStrLn "Definition complete"
                                    return env
                                | otherwise         -> go env'

readline = do
    mline <- Readline.readline "> "
    case mline of
        Nothing -> return Nothing
        Just line -> Readline.addHistory line >> return (Just line)

parseProof = (,) <$> (fromIntegral <$> P.natural lex) <*> P.choice [
    "done"     --> pure (const Proof.Done),
    "exact"    --> Proof.Exact <$> hyp <*> goal,
    "witness"  --> Proof.Witness <$> label <*> expr,
    "flatten"  --> Proof.Flatten <$> hyp <*> list expr <*> list label <*> list label <*> pure () 
    ]
    where
    infix 0 --> 
    n --> p = P.reserved lex n *> (p <*> pure ())
    lex = Parser.lex
    label = P.identifier lex
    hyp = Proof.Hyp <$> label
    goal = Proof.Goal <$> label
    expr = Parser.expr
    list p = P.parens lex $ p `P.sepBy` (P.symbol lex ",")

indent :: String -> String -> String
indent by = unlines . map (by ++) . lines
 
display :: Environment -> IO ()
display env = 
    forM_ (zip [0..] (goals env)) $ \(i,(c,_)) ->
        putStrLn $ show i ++ "::\n" ++ indent "  " (showClauseV c)

tactic :: Proof.Proof () -> Pf
tactic p = constructor p . Roll . O $ Suspend ()

applyProof :: Int -> Pf -> Environment -> Error Environment
applyProof i pf env = do
    let conts = goals env
    guard $ i < length conts
    let pf' = snd (conts !! i) pf
    Environment (clause env) . getConst <$> proofCheck pf' (clause env)
