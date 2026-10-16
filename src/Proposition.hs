module Proposition where

-- import Utils

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
