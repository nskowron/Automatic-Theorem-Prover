module FOL where

import Proposition

import Data.Kind ( Type )
import Data.Type.Equality ( (:~:)(..) )


-- === Equals === --
type n :=: m = n :~: m


-- === Predicate === --
data Predicate p x where
    Predicate :: Eval p x -> Predicate p x

type family Eval p (x :: a)


-- === Quantifiers === --
data Forall a p where
    Forall :: (forall (x :: a). Predicate p x) -> Forall a p

data Exists a p where
    Exists :: forall a (x :: a) p. Predicate p x -> Exists a p
