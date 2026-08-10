{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Prover where

import HSet
import Proposition
import Node
import Search

import Data.Kind ( Type )


-- Provable - describes provable propositions
class Provable a where
    prove :: a

-- each proof search tree node is (maybe) a function that
-- takes in the context and returns proof of a proposition
instance 
    ( tree ~ FromMaybe Unprovable (SearchNode '[] proposition '[] Search)
    , Inferable tree '[] proposition
    ) => Provable proposition where
    prove = infer @tree @'[] @proposition HNil


-- helper
printProof :: Maybe a -> String
printProof Nothing = "Nothing"
printProof (Just _) = "Proof Successful"
