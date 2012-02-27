module Sequent.Fixpoint where

newtype Mu f = Roll { unroll :: f (Mu f) }

cata :: (Functor f) => (f r -> r) -> Mu f -> r
cata f m = f (fmap (cata f) (unroll m))

data Suspension a f
    = Suspend a
    | Normal  f

instance Functor (Suspension a) where
    fmap f (Suspend a) = Suspend a
    fmap f (Normal a) = Normal (f a)
