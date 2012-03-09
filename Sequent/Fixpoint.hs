{-# LANGUAGE FlexibleContexts, UndecidableInstances, TypeOperators #-}

module Sequent.Fixpoint where

import Prelude hiding (sequence)
import Control.Monad (liftM, ap, MonadPlus(..))
import Control.Applicative
import Control.Arrow
import Control.Monad.Identity (Identity)
import Data.Traversable

newtype (f :. g) x = O { unO :: f (g x) }
    deriving Show

instance (Functor f, Functor g) => Functor (f :. g) where
    fmap f (O a) = O ((fmap.fmap) f a)

instance (Applicative f, Applicative g) => Applicative (f :. g) where
    pure = O . pure . pure
    O f <*> O x = O (liftA2 (<*>) f x)

newtype Mu f = Roll { unroll :: f (Mu f) }

instance (Show (f (Mu f))) => Show (Mu f) where
    show = show . unroll

cata :: (Functor f) => (f r -> r) -> Mu f -> r
cata f = cxCata (f . fmap fst)

cxCata :: (Functor f) => (f (r, Mu f) -> r) -> Mu f -> r
cxCata f m = f (fmap (cxCata f &&& id) (unroll m))

sequenceMu :: (Monad f, Traversable g) => Mu (f :. g) -> f (Mu g)
sequenceMu = unO . unroll            -- f (g (Mu (f :. g)))
         >>> (liftM.fmap) sequenceMu -- f (g (f (Mu g)))
         >>> liftM sequence          -- f (f (g (Mu g)) 
         >>> (id =<<)                -- f (g (Mu g))   
         >>> liftM Roll              -- f (Mu g)       

data Error a = Error String | Ok a

instance Functor Error where
    fmap f (Error s) = Error s
    fmap f (Ok a) = Ok (f a)

instance Monad Error where
    fail = Error
    return = Ok
    Error s >>= f = Error s
    Ok a    >>= f = f a

instance Applicative Error where
    pure = return
    (<*>) = ap

instance MonadPlus Error where
    mzero = Error "mzero"
    Error a `mplus` Error b = Error (a ++ "\n" ++ b)
    Error a `mplus` Ok b = Ok b
    Ok a `mplus` Ok b = Ok a

data Suspension a f
    = Suspend a
    | Normal  f
    deriving Show

instance Functor (Suspension a) where
    fmap f (Suspend a) = Suspend a
    fmap f (Normal a) = Normal (f a)

instance Monad (Suspension a) where
    return = Normal
    Suspend a >>= f = Suspend a
    Normal x  >>= f = f x

instance Applicative (Suspension a) where
    pure = return
    (<*>) = ap

{-  -- WTF, on one 6.12.1 it works and on another it doesn't. Maybe library version shit.
instance Applicative Identity where
    pure = return
    (<*>) = ap
-}

newtype SuspM f a = SuspM { getSuspM :: Mu (Suspension a :. f) }

instance (Functor f) => Functor (SuspM f) where
    -- cata :: (Suspension a (f SuspM) -> r) -> SuspM f a -> r
    fmap f = SuspM . cata alg . getSuspM
        where
        alg (O (Suspend x)) = Roll (O (Suspend (f x)))
        alg (O (Normal r)) = Roll (O (Normal r))

instance (Functor f) => Monad (SuspM f) where
    return = SuspM . Roll . O . Suspend
    t >>= f = joinSuspM (fmap f t)

instance (Functor f) => Applicative (SuspM f) where
    pure = return
    (<*>) = ap

joinSuspM :: (Functor f) => SuspM f (SuspM f a) -> SuspM f a
joinSuspM  = SuspM . cata alg . getSuspM
    where
    alg (O (Suspend x)) = getSuspM x
    alg (O (Normal r)) = Roll (O (Normal r))
