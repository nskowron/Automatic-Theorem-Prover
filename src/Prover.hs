module Prover where

import Utils
import Proposition
import Node
import Search

import Data.HList ( HList( HNil ) )
import Data.Kind ( Type )
import GHC.TypeLits ( Nat )


-- === Provable === --
class Provable a where
    prove :: a
    emit :: IO ()

instance 
    ( tree ~ FromMaybe Unprovable (MakeNode Search '[] proposition '[] 0)
    , Inferable tree '[] proposition
    -- , ShowType '(tree, proposition)
    ) => Provable proposition where
    prove = infer @tree @'[] @proposition HNil
    -- emit = putStrLn $ showType @'(tree, proposition)
