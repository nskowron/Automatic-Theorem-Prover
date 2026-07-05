{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}

module Prover where


import Proposition
import Search

import Control.Monad ( join )
import Data.HList ( HList(..) )


-- Provable - describes provable propositions
class Provable a where
    prove :: Maybe a

-- each proof search tree node is (maybe) a function that
-- takes in the context and returns proof of a proposition
instance (Searchable (SearchNodes '[] a '[])) => Provable a where
    prove = join <$> (search @(SearchNodes '[] a '[])) <*> pure HNil


-- helper
printProof :: Maybe a -> String
printProof Nothing = "Nothing"
printProof (Just _) = "Proof Successful"
