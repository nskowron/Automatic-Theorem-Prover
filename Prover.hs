{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}

module Prover where


import Proposition
import Search

import Data.HList ( HList(..) )


-- Provable - describes provable propositions
class Provable a where
    prove :: Maybe a

-- each proof search tree node is (maybe) a function that
-- takes in the context and returns proof of a proposition
instance (Searchable (HList '[] -> a)) => Provable a where
    prove = fmap (\proof -> proof HNil) (search @(HList '[] -> a))


-- helper
printProof :: Maybe a -> String
printProof Nothing = "Nothing"
printProof (Just _) = "Proof Successful"
