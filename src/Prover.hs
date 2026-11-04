module Prover where

import SearchUtils
import Utils
import Proposition
import FOL
import Node
import Search
import NewSearch

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
    , fv ~ X Z
    , env ~ '[ '(fv, True) ]
    , config ~ Config context context fv
    , tree ~ FromMaybe Unprovable (TryInfer '[Intro] proposition config Nothing)
    , Inferable tree env '[] proposition
    -- , ShowType '(tree, proposition)
    ) => Provable proposition where
    prove = infer @tree @env @context @proposition HNil
    -- emit = putStrLn $ showType @'(tree, proposition)
