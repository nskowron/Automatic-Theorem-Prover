{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveDataTypeable #-}

module Prover where

import Data.Typeable


data Assumption where
    Assumption :: (Proposition a) => a -> Assumption

class (Typeable a) => Proposition a where
    prove :: [Assumption] -> a

newtype Impl a b = Impl (a -> b)

instance (Proposition a, Proposition b) => Proposition (Impl a b) where
    prove context = Impl $ \x -> (prove :: [Assumption] -> b) (Assumption x : context)

instance Proposition Int where
    prove (Assumption c : cs) = case cast c of
        Just x  -> x :: Int
        Nothing -> prove cs
    prove [] = error "Not found"
