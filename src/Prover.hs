{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Prover where

import HSet
import Proposition
import Inference

import Data.Kind ( Type )


-- Provable - describes provable propositions
class Provable a where
    prove :: Maybe a

-- each proof search tree node is (maybe) a function that
-- takes in the context and returns proof of a proposition
instance 
    ( Inferable (a :: Type) ('[] :: [Type]) ('[] :: [(Type, Type, [Type])])
    ) => Provable (a :: Type) where
    prove = infer @(a :: Type) @('[] :: [Type]) @('[] :: [(Type, Type, [Type])]) <*> pure HNil


-- helper
printProof :: Maybe a -> String
printProof Nothing = "Nothing"
printProof (Just _) = "Proof Successful"
