module Proposition where

import Utils

import Data.Void ( Void )


-- === Propositions === --
type True = ()
type False = Void
type a `Impl` b = a -> b
type a `And` b = (a, b)
type a `Or` b = Either a b
type Not a = a -> False

data A
data B
data C


-- === ShowType === --
instance ShowType True where
    showType = "True"

instance ShowType False where
    showType = "False"

instance {-# OVERLAPPABLE #-}
    ( ShowType a
    , ShowType b
    ) => ShowType (a -> b) where
    showType = "(" ++ showType @a ++ " -> " ++ showType @b ++ ")"

instance
    ( ShowType a
    , ShowType b
    ) => ShowType (a `And` b) where
    showType = "(" ++ showType @a ++ " And " ++ showType @b ++ ")"

instance
    ( ShowType a
    , ShowType b
    ) => ShowType (a `Or` b) where
    showType = "(" ++ showType @a ++ " Or " ++ showType @b ++ ")"

instance {-# OVERLAPPING #-}
    ( ShowType a
    ) => ShowType (Not a) where
    showType = "!" ++ showType @a

instance ShowType A where
    showType = "A"

instance ShowType B where
    showType = "B"

instance ShowType C where
    showType = "C"
