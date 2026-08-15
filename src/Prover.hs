{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Prover where

import Utils
import Proposition
import Node
import Search

import Data.HList ( HList( HNil ) )
import Data.Kind ( Type )


-- === Provable === --
class Proposition a => Provable a where
    prove :: a
    emit :: String

instance 
    ( tree ~ FromMaybe Unprovable (MakeNode Search '[] proposition '[])
    , Inferable tree '[] proposition
    , Proposition proposition
    ) => Provable proposition where
    prove = infer @tree @'[] @proposition HNil
    emit = Node.emit @tree @'[] @proposition 0
