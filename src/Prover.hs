{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}

module Prover where


import HSet
import Proposition
import Inference

-- Provable - describes provable propositions
class Provable a where
    prove :: Maybe a

-- each proof search tree node is (maybe) a function that
-- takes in the context and returns proof of a proposition
instance 
    ( Inferable a '[]
    ) => Provable a where
    prove = infer @a @'[] <*> pure HNil


-- helper
printProof :: Maybe a -> String
printProof Nothing = "Nothing"
printProof (Just _) = "Proof Successful"
