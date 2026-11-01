module Prover where

import SearchUtils
import Utils
import Proposition
import FOL
import Node
import Search

import Data.HList ( HList( HNil ) )
import Data.Kind ( Type )
import Data.Type.Nat


-- === Provable === --
class Provable a where
    prove :: a
    -- emit :: IO ()

instance 
    ( parents ~ '[]
    , context ~ '[]
    , n ~ Z
    , env ~ '[ '(X n, True) ]
    , tree ~ FromMaybe Unprovable (MakeNode Search context proposition n parents)
    , Apply proposition env ~ proposition
    , Inferable tree env context proposition
    -- , ShowType '(tree, proposition)
    ) => Provable proposition where
    prove = infer @tree @env @context @proposition HNil
    -- emit = putStrLn $ showType @'(tree, proposition)
