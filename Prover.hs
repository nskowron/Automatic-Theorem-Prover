{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveDataTypeable #-}

module Prover where

import Data.Typeable

-- TODO:
-- try Proxy
-- add string context to proofs

-- Assumption
-- used to store assumed propositions heterogenously in context
-- problem: retrieving the types later and pattern matching
-- solutions: casting or try Proxy
data Assumption where
    Assumption :: (Proposition a) => a -> Assumption

-- Proposition
-- only types that are an instance of this class can be proven
class (Typeable a) => Proposition a where
    prove :: [Assumption] -> a

-- True
instance Proposition () where
    prove _ = ()

-- Implication
newtype Impl a b = Impl (a -> b)

-- problem: stopping the creation of the function
-- how to check if b is provable without introducing x?
-- solutions: try Proxy or introduce a Var type to create concrete but shadow variables
instance (Proposition a, Proposition b) => Proposition (Impl a b) where
    -- prove b while assuming a
    prove context = Impl $ \x -> prove (Assumption x : context) :: b

-- Int
-- testing the pattern matching solutions
-- may be used later for FOL
instance Proposition Int where
    -- prove only when it's assumed
    prove (Assumption c : cs) = case cast c of
        Just x  -> x :: Int
        Nothing -> prove cs
    prove [] = error "Not found"


-- helper
eval :: Impl a b -> a -> b
eval (Impl f) x = f x
