module FOL where

import Eval
import Proposition

import Data.Kind ( Type )
import Data.Type.Equality ( (:~:)(..) )
import GHC.TypeLits ( Symbol )


-- === Equals === --
type n :=: m = n :~: m


-- === Quantifiers === --
data Forall x a p where
    Forall :: (forall (v :: a). Eval p x v) -> Forall x a p

data Exists x a p where
    Exists :: forall x a (v :: a) p. Eval p x v -> Exists x a p


-- === Variable === --
data Variable where
    Any :: Symbol -> Variable
    All :: Symbol -> Variable
