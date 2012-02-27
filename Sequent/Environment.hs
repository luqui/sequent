{-# LANGUAGE GeneralizedNewtypeDeriving #-}

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
import qualified System.Console.SimpleLineEditor as Readline

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


sequent :: String -> IO Environment
sequent s = do
    case Parser.parse Parser.clause s of
        Left err -> fail $ show err
        Right cl -> interactive (Environment cl [(cl, id)])

interactive :: Environment -> IO Environment
interactive = \env -> do
    Readline.initialise
    env' <- go env
    Readline.restore
    return env'
    where
    go env = do
        display env
        maybeLine <- Readline.getLineEdited "> "
        case maybeLine of
            Nothing -> return env
            Just line -> do
                case P.parse parseProof "<input>" line of
                    Left err -> print err >> go env
                    Right (n,proof) -> 
                        case applyProof n (tactic proof) env of
                            Nothing -> putStrLn "Proof error" >> go env
                            Just env'
                                | null (goals env') -> return env
                                | otherwise         -> go env'


parseProof = (,) <$> (fromIntegral <$> P.natural lex) <*> P.choice [
    "done"     --> pure (const Proof.Done),
    "exact"    --> Proof.Exact <$> hyp <*> goal,
    "instance" --> Proof.Instance <$> expr <*> ((,) <$> hyp <*> hyp) <*> label,
    "witness"  --> Proof.Witness <$> expr <*> goal,
    "modus"    --> Proof.ModusGoal <$> ((,) <$> hyp <*> hyp) <*> label <*> label,
    "flatten"  --> Proof.FlattenHyp <$> hyp <*> many label,
    "drop"     --> Proof.DropHyp <$> hyp ]
    where
    lex = Parser.lex
    infix 0 --> 
    n --> p = P.reserved lex n *> (p <*> pure ())
    label = P.natural lex
    hyp = Proof.Hyp <$> label
    goal = Proof.Goal <$> label
    expr = Parser.expr
    
 
display :: Environment -> IO ()
display env = 
    forM_ (zip [0..] (goals env)) $ \(i,(c,_)) ->
        putStrLn $ show i ++ ":: " ++ showClauseV c

tactic :: Proof.Proof () -> Pf
tactic = Roll . PfLink . Normal . fmap (const . Roll . PfLink $ Suspend ())

applyProof :: Int -> Pf -> Environment -> Maybe Environment
applyProof i pf env = do
    let conts = goals env
    guard $ i < length conts
    let pf' = snd (conts !! i) pf
    Environment (clause env) . getConst <$> proofCheck pf' (clause env)
