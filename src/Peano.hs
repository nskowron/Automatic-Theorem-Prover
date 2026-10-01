module Peano where

import FOL

import Data.Type.Nat ( Nat(..) )
import Data.Type.Equality ( (:~:)(..) )


-- === Arithmetics === --
type family (n :: Nat) :+: (m :: Nat) where
    Z :+: m = m
    (S n) :+: m = S (n :+: m)

type family (n :: Nat) :*: (m :: Nat) where
    Z :*: m = Z
    (S n) :*: m = m :+: (n :*: m)


-- === Experiments === --
class Inducible (n :: Nat) where
    induction
        :: f Z
        -> (forall m. f m -> f (S m))
        -> f n

instance Inducible Z where
    induction base _ = base

instance
    ( Inducible n
    ) => Inducible (S n) where
    induction base step = step (induction base step)
