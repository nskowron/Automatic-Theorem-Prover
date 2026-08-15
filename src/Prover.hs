module Prover where

import Utils
import Proposition hiding ( display )
import Node
import Search

import Data.HList ( HList( HNil ) )
import Data.Kind ( Type )


-- === Provable === --
class Proposition a => Provable a where
    prove :: a
    emit :: IO ()

instance 
    ( tree ~ FromMaybe Unprovable (MakeNode Search '[] proposition '[])
    , Inferable tree '[] proposition
    , Proposition proposition
    ) => Provable proposition where
    prove = infer @tree @'[] @proposition HNil
    emit = putStrLn $ display @tree @'[] @proposition 0
