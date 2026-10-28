module FOL where

import Utils
import Proposition

import ACFp ( F, (:+:), (:-:), (:*:), (:/:), (:^:) )
import qualified ACFp ( Eval )

import Data.Kind ( Type )
import Data.Type.Equality ( (:~:)(..) )
import GHC.TypeLits ( Symbol )


-- === Var === --
data Var (x :: Symbol)


-- === Equals === --
type n :=: m = n :~: m


-- === Quantifiers === --
data Forall (x :: Symbol) (p :: Type) where
    Forall :: p -> Forall x p

data Exists (x :: Symbol) (p :: Type) where
    Exists :: forall (t :: Type) (x :: Symbol) (p :: Type).
        Substitute p (Var x) t -> Exists x p


-- === Substitute === --
type family Substitute p x y where

    Substitute p x x = p
    Substitute x x y = y

    Substitute (a -> b) x y = Substitute a x y -> Substitute b x y
    Substitute (a `And` b) x y = Substitute a x y `And` Substitute b x y
    Substitute (a `Or` b) x y = Substitute a x y `Or` Substitute b x y

    Substitute (a :=: b) x y = Substitute a x y :=: Substitute b x y

    Substitute (Forall x p) (Var x) y = Forall x p -- allow variable shadowing
    Substitute (Forall z p) x y = Forall z (Substitute p x y)
    Substitute (Exists x p) (Var x) y = Exists x p -- allow variable shadowing
    Substitute (Exists z p) x y = Exists z (Substitute p x y)

    Substitute (a :+: b) x y = Substitute a x y :+: Substitute b x y
    Substitute (a :-: b) x y = Substitute a x y :-: Substitute b x y
    Substitute (a :*: b) x y = Substitute a x y :*: Substitute b x y
    Substitute (a :/: b) x y = Substitute a x y :/: Substitute b x y
    Substitute (a :^: b) x y = Substitute a x y :^: Substitute b x y

    Substitute p x y = p
