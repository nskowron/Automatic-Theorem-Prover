module Inference where

import Proposition


-- === Intro === --
introAnd :: a -> b -> a `And` b
introAnd = (,)

introOrLeft :: a -> a `Or` b
introOrLeft = Left

introOrRight :: b -> a `Or` b
introOrRight = Right


-- === Elim === --
elimAndLeft :: a `And` b -> a
elimAndLeft = fst

elimAndRight :: a `And` b -> b
elimAndRight = snd

elimOr :: a `Or` b -> (a -> c) -> (b -> c) -> c
elimOr (Left a) f _ = f a
elimOr (Right b) _ f = f b
