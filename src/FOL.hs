module FOL where

import Utils
import Proposition

import ACFp ( F, (:+:), (:-:), (:*:), (:/:), (:^:) )
import qualified ACFp ( Eval )

import Data.Kind ( Type )
import Data.Type.Equality ( (:~:)(..) )
import Data.Proxy ( Proxy(..) )
import GHC.TypeLits ( Symbol )


-- === Equals === --
type n :=: m = n :~: m


-- === Variable Domain === --
data Var (x :: Type) :: Type 


-- === Quantifiers === --
data Forall (x :: Type) (a :: d -> Type) (p :: Type) where
    Forall :: (forall t. Predicate p x (a t)) -> Forall x a p

data Exists (x :: Type) (a :: d -> Type) (p :: Type) where
    Exists :: forall t x a p. Predicate p x (a t) -> Exists x a p


-- === Predicate === --
data Predicate (p :: Type) (x :: Type) (t :: Type) where
    Predicate :: Substitute p x t -> Predicate p x t


-- === Substitute === --
type family Substitute p x t where

    Substitute x x t = t

    Substitute (a -> b) x t = Substitute a x t -> Substitute b x t
    Substitute (a `And` b) x t = Substitute a x t `And` Substitute b x t
    Substitute (a `Or` b) x t = Substitute a x t `Or` Substitute b x t

    Substitute (a :=: b) x t = Substitute a x t :=: Substitute b x t

    Substitute (Predicate p x s) x t = Predicate p x (Substitute s x t) -- allow variable shadowing
    Substitute (Predicate p y s) x t = Predicate (Substitute p x t) y (Substitute s x t)
    Substitute (Forall x a p) x t = Forall x a p -- allow tariable shadowing
    Substitute (Forall y a p) x t = Forall y a (Substitute p x t)
    Substitute (Exists x a p) x t = Exists x a p -- allow tariable shadowing
    Substitute (Exists y a p) x t = Exists y a (Substitute p x t)

    Substitute p x t = p
