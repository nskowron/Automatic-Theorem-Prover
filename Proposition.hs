module Proposition where

import Data.Void ( Void )

-- Proposition Types
type True = ()
type False = Void
type Impl a b = a -> b
type And a b = (a, b)
type Or a b = Either a b
type Not a = a -> False
newtype PS a = PS a -- Propositional Symbol

-- Proposition Class
class Proposition a

instance Proposition True
instance Proposition False
instance (Proposition a, Proposition b) => Proposition (a `Impl` b)
-- TODO: rest