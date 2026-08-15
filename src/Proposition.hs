{-# LANGUAGE AllowAmbiguousTypes #-}

module Proposition where

import Data.Void ( Void )

import Prelude hiding( show )


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
    show :: String

instance Proposition True where
    show = "True"

instance Proposition False where
    show = "False"

instance {-# OVERLAPPABLE #-}
    ( Proposition a
    , Proposition b
    ) => Proposition (a -> b) where
    show = "(" ++ show @a ++ " -> " ++ show @b ++ ")"

instance
    ( Proposition a
    , Proposition b
    ) => Proposition (a `And` b) where
    show = "(" ++ show @a ++ " And " ++ show @b ++ ")"

instance
    ( Proposition a
    , Proposition b
    ) => Proposition (a `Or` b) where
    show = "(" ++ show @a ++ " Or " ++ show @b ++ ")"

instance {-# OVERLAPPING #-}
    ( Proposition a
    ) => Proposition (Not a) where
    show = "!" ++ show @a

instance Proposition A where
    show = "A"

instance Proposition B where
    show = "B"

instance Proposition C where
    show = "C"
