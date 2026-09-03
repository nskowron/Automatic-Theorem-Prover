module Prover where

import Utils
import Proposition
import Node
import Search

import Data.HList ( HList( HNil ) )
import Data.Kind ( Type )


-- === Provable === --
class Provable a where
    prove :: a

instance 
    ( tree ~ FromMaybe Unprovable (MakeNode Search '[] proposition '[])
    , Inferable tree '[] proposition
    ) => Provable proposition where
    prove = infer @tree @'[] @proposition HNil
