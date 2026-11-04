module SearchUtils where

import Utils
import Proposition
import FOL

import Data.Kind ( Type )
import Data.Type.Nat


-- === FV X === --
data X (n :: Nat)


-- === Config === --
data Config (full_context :: [Type]) (search_context :: [Type]) (free_variable :: Type)

type family SubstituteAll ps x t where
    SubstituteAll '[] _ _ = '[]
    SubstituteAll (p ': ps) x t = Substitute p x t ': SubstituteAll ps x t

type family GetFullContext config where
    GetFullContext (Config full_context _ _) = full_context

type family GetSearchContext config where
    GetSearchContext (Config _ search_context _) = search_context

type family GetFV config where
    GetFV (Config _ _ free_variable) = free_variable

type family GetNextFV config where
    GetNextFV (Config _ _ (X n)) = X (S n)

type family IncrementFV config where
    IncrementFV (Config full_context search_context (X n)) =
        Config full_context search_context (X (S n))

type family Assume a config where
    Assume a (Config full_context search_context free_variable) =
        Config (a ': full_context) (If (Member a search_context) True a ': search_context) free_variable

type family Unassume a config where
    Unassume a (Config full_context search_context free_variable) =
        Config full_context (SubstituteAll search_context a True) free_variable


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
    Map k e ('(x, k) ': m) = '(x, e) ': m
    Map k e ('(x, f) ': m) = '(x, f) ': Map k e m

-- type family Assume p c where
--     Assume True '[] = '[]
--     Assume p '[] = '[ '(p, Z) ]
--     Assume p ('(p, n) ': c) = '(p, S n) ': Assume True c
--     Assume p ('(q, n) ': c) = '(q, S n) ': Assume p c

-- type family Unassume p c where
--     Unassume p '[] = '[]
--     Unassume p ('(p, _) ': c) = Unassume p c
--     Unassume p ('(q, n) ': c) = '(Substitute q p True, n) ': Unassume p c

-- type family Premises c where
--     Premises '[] = '[]
--     Premises ('(p, _) ': c) = p ': Premises c
