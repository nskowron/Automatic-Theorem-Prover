{-# LANGUAGE AllowAmbiguousTypes #-}

module Proposition where

import Data.Void ( Void )


-- === Propositions === --
type True = ()
type False = Void
type Impl a b = a -> b
type And a b = (a, b)
type Or a b = Either a b
type Not a = a -> False

data A
data B
data C


-- === Proposition === --
class Proposition a where
    display :: String

instance Proposition True where
    display = "True"

instance Proposition False where
    display = "False"

instance {-# OVERLAPPABLE #-}
    ( Proposition a
    , Proposition b
    ) => Proposition (a -> b) where
    display = "(" ++ display @a ++ " -> " ++ display @b ++ ")"

instance
    ( Proposition a
    , Proposition b
    ) => Proposition (a `And` b) where
    display = "(" ++ display @a ++ " And " ++ display @b ++ ")"

instance
    ( Proposition a
    , Proposition b
    ) => Proposition (a `Or` b) where
    display = "(" ++ display @a ++ " Or " ++ display @b ++ ")"

instance {-# OVERLAPPING #-}
    ( Proposition a
    ) => Proposition (Not a) where
    display = "!" ++ display @a

instance Proposition A where
    display = "A"

instance Proposition B where
    display = "B"

instance Proposition C where
    display = "C"
