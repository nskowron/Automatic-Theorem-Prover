module SearchUtils where

import Utils
import Proposition
import FOL

import Data.Kind ( Type )
import Data.Type.Nat


-- === FV X === --
data X (n :: Nat)


-- === Apply === --
type family Apply (p :: Type) (env :: [(Type, Type)]) where

    Apply (X n) env = Get (X n) env

    Apply (a -> b) env = Apply a env -> Apply b env
    Apply (a `And` b) env = Apply a env `And` Apply b env
    Apply (a `Or` b) env = Apply a env `Or` Apply b env

    Apply (a :=: b) env = Apply a env :=: Apply b env

    Apply (Predicate p x t) env = Predicate (Apply p ('(x, x) ': env)) x (Apply t env)
    Apply (Forall x a p) env = Forall x a (Apply p env)
    Apply (Exists x a p) env = Exists x a (Apply p env)

    Apply p env = p


-- === Utils === --
type family Map k e m where
    Map (X n) e m = m
    -- Map k e ('(k, f) ': m) = '(k, e) ': m
    Map k e ('(x, k) ': m) = '(x, e) ': m
    Map k e ('(x, f) ': m) = '(x, f) ': Map k e m
