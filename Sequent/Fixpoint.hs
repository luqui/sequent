{-# LANGUAGE FlexibleContexts, UndecidableInstances #-}

module Sequent.Fixpoint where

import Control.Arrow

newtype Mu f = Roll { unroll :: f (Mu f) }

instance (Show (f (Mu f))) => Show (Mu f) where
    show = show . unroll

cata :: (Functor f) => (f r -> r) -> Mu f -> r
cata f = cxCata (f . fmap fst)

cxCata :: (Functor f) => (f (r, Mu f) -> r) -> Mu f -> r
cxCata f m = f (fmap (cxCata f &&& id) (unroll m))
    

data Suspension a f
    = Suspend a
    | Normal  f
    deriving Show

instance Functor (Suspension a) where
    fmap f (Suspend a) = Suspend a
    fmap f (Normal a) = Normal (f a)
