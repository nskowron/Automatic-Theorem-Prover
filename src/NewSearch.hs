module NewSearch where

import Utils
import SearchUtils
import Node
import Proposition
import FOL

import Data.Kind ( Type )
import Data.Type.Nat ( Nat(..) )


data Rule = Proj | Intro | Elim
type Find = '[Proj, Elim, Intro]
type Search = '[Proj, Intro, Elim]

type family TryInfer (rule_order :: [Rule]) (goal :: Type) config (last_node :: Maybe Node) where

    TryInfer _ _ _ (Just node) = Just node
    TryInfer '[] _ _ Nothing = Nothing

    TryInfer (Proj ': rule_order) goal config Nothing =
        TryInfer rule_order goal config (TryProj Z goal (GetFullContext config))

    TryInfer (Intro ': rule_order) goal config Nothing =
        TryInfer rule_order goal config (TryIntro goal config '[])

    TryInfer (Elim ': rule_order) goal config Nothing =
        TryInfer rule_order goal config (TryElim (GetFullContext config) (GetSearchContext config) goal config Nothing)

type family TryProj (n :: Nat) (goal :: Type) (context :: [Type]) where

    TryProj _ _ '[] = Nothing
    TryProj n goal (goal ': _) = Just (Project n)
    TryProj n goal (premise ': context) = TryProj (S n) goal context

type family TryIntro (goal :: Type) config (subgoals :: [Maybe Node]) where

    TryIntro _ _ '[Nothing] = Nothing
    TryIntro _ _ '[Just _, Nothing] = Nothing

    -- Intro True --
    TryIntro True config '[] =
        Just IntroTrue

    -- Intro Impl --
    TryIntro (a -> b) config '[] =
        TryIntro (a -> b) config '[TryInfer Search b (Assume a config) Nothing]

    TryIntro (a -> b) config '[Just node] =
        Just (IntroImpl node)

    -- Intro And --
    TryIntro (a `And` b) config '[] =
        TryIntro (a `And` b) config '[TryInfer Search a config Nothing]
    
    TryIntro (a `And` b) config '[Just node_left] =
        TryIntro (a `And` b) config '[Just node_left, TryInfer Search b config Nothing]

    TryIntro (a `And` b) config '[Just node_left,  Just node_right] =
        Just (IntroAnd node_left node_right)

    -- Intro Or --
    TryIntro (a `Or` b) config '[] =
        TryIntroOr (a `Or` b) config '[]

    -- Intro Eq --
    TryIntro (x :=: x) config '[] =
        Just Reflexivity

    -- Intro Forall --
    TryIntro (Forall x a p) config '[] =
        TryIntro (Forall x a p) config '[TryInfer Search (Substitute p x (GetNextFV config)) (IncrementFV config) Nothing]

    TryIntro (Forall x a p) config '[Just node] =
        Just (IntroForall (IntroPredicate node))

    -- Intro Exists --
    TryIntro (Exists x a p) config '[] =
        TryIntroExists (GetNextFV config) (Exists x a p) config Nothing

    -- Fallback --
    TryIntro _ _ _ = Nothing

type family TryIntroOr (goal :: Type) config (subgoals :: [Maybe Node]) where

    TryIntroOr (a `Or` b) config '[] =
        TryIntroOr (a `Or` b) config '[TryInfer Search a config Nothing]

    TryIntroOr (a `Or` b) config '[Just node] =
        Just (IntroOrLeft node)

    TryIntroOr (a `Or` b) config '[Nothing] =
        TryIntroOr (a `Or` b) config '[Nothing, TryInfer Search b config Nothing]

    TryIntroOr (a `Or` b) config '[Nothing, Just node] =
        Just (IntroOrRight node)

    TryIntroOr _ _ '[Nothing, Nothing] = Nothing

type family TryIntroExists (witness :: Type) (goal :: Type) config (last_node :: Maybe Node) where

    TryIntroExists witness _ _ (Just node) = Just (IntroExists witness (IntroPredicate node))
    TryIntroExists (X Z) _ _ Nothing = Nothing

    TryIntroExists (X (S n)) (Exists x a p) config Nothing =
        TryIntroExists (X n) (Exists x a p) config (TryInfer Search (Substitute p x (X n)) config Nothing)

type family TryElim (full_context :: [Type]) (search_context :: [Type]) (goal :: Type) config (last_node :: Maybe Node) where

    TryElim _ _ _ _ (Just node) = Just node
    TryElim '[] '[] _ _ Nothing = Nothing

    TryElim (_ ': full_context) (True ': search_context) goal config Nothing =
        TryElim full_context search_context goal config Nothing

    TryElim ((a -> b) ': full_context) ((p -> q) ': search_context) goal config Nothing =
        TryElim (b ': full_context) (q ': search_context) goal config (TryElimPremise (a -> b) goal config '[])

    TryElim ((a `And` b) ': full_context) ((p `And` q) ': search_context) goal config Nothing =
        TryElim (a ': b ': full_context) (p ': q ': search_context) goal config (TryElimPremise (a `And` b) goal config '[])

    TryElim ((a `Or` b) ': full_context) ((p `Or` q) ': search_context) goal config Nothing =
        TryElim full_context search_context goal config (TryElimPremise (a `Or` b) goal config '[])

    TryElim (Predicate p x t ': full_context) (Predicate q x t ': search_context) goal config Nothing =
        TryElim (Substitute p x t ': full_context) (Substitute q x t ': search_context) goal config (TryElimPremise (Predicate p x t) goal config '[])

    TryElim (a ': full_context) (p ': search_context) goal config Nothing =
        TryElim full_context search_context goal config (TryElimPremise a goal config '[])

type family TryElimPremise (full_premise :: Type) (goal :: Type) config (subgoals :: [Maybe Node]) where

    -- Subgoal Search Failed --
    TryElimPremise _ _ _ '[Nothing] = Nothing
    TryElimPremise _ _ _ '[Just _, Nothing] = Nothing
    TryElimPremise _ _ _ '[Just _, Just _, Nothing] = Nothing

    -- Elim False --
    TryElimPremise False goal config '[] =
        TryElimPremise False goal config '[TryInfer Find False config Nothing]

    TryElimPremise False goal config '[Just node] =
        Just (ElimFalse node)

    -- Elim Impl --
    TryElimPremise (a -> b) b config '[] =
        TryElimPremise (a -> b) b config '[TryInfer Find (a -> b) config Nothing]

    TryElimPremise (a -> b) b config '[Just node_impl] =
        TryElimPremise (a -> b) b config '[Just node_impl, TryInfer Search a config Nothing]

    TryElimPremise (a -> b) b config '[Just node_impl, Just node_arg] =
        Just (ElimImpl (a -> b) node_impl node_arg)

    -- Elim And Left --
    TryElimPremise (a `And` b) a config '[] =
        TryElimPremise (a `And` b) a config '[TryInfer Find (a `And` b) config Nothing]

    TryElimPremise (a `And` b) a config '[Just node] =
        Just (ElimAndLeft (a `And` b) node)

    -- Elim And Right --
    TryElimPremise (a `And` b) b config '[] =
        TryElimPremise (a `And` b) b config '[TryInfer Find (a `And` b) config Nothing]

    TryElimPremise (a `And` b) b config '[Just node] =
        Just (ElimAndRight (a `And` b) node)

    -- Elim Or --
    TryElimPremise (a `Or` b) goal config '[] =
        TryElimPremise (a `Or` b) goal (Unassume (a `Or` b) config) '[TryInfer Find (a `Or` b) config Nothing]

    TryElimPremise (a `Or` b) goal config '[Just node_or] =
        TryElimPremise (a `Or` b) goal config '[Just node_or, TryInfer Search goal (Assume a config) Nothing]

    TryElimPremise (a `Or` b) goal config '[Just node_or, Just node_left] =
        TryElimPremise (a `Or` b) goal config '[Just node_or,  Just node_left, TryInfer Search goal (Assume b config) Nothing]

    TryElimPremise (a `Or` b) goal config '[Just node_or, Just node_left, Just node_right] =
        Just (ElimOr (a `Or` b) node_or node_left node_right)

    -- Elim Eq --
    TryElimPremise (x :=: y) goal config '[] =
        TryElimEq (x :=: y) goal config '[]

    -- Elim Predicate --
    TryElimPremise (Predicate p x t) goal config '[] =
        TryElimPred (Predicate p x t) goal config (Equal goal (Substitute p x t)) '[]

    -- Elim Forall --
    TryElimPremise (Forall x a p) goal config '[] =
        TryElimForall (GetNextFV config) (Forall x a p) goal config False '[TryInfer Find (Forall x a p) config Nothing]

    -- Elim Exists --
    TryElimPremise (Exists x a p) goal config '[] =
        TryElimPremise (Exists p a x) goal (Unassume (Exists x a p) config) '[TryInfer Find (Exists x a p) config Nothing]

    TryElimPremise (Exists x a p) goal config '[Just node_exists] =
        TryElimPremise (Exists x a p) goal config '[Just node_exists, TryInfer Search goal (Assume (Substitute p x (GetNextFV config)) (IncrementFV config)) Nothing]

    TryElimPremise (Exists x a p) goal config '[Just node_exists, Just node_c] =
        Just (ElimExists (Exists x a p) node_exists node_c)

    -- Fallback --
    TryElimPremise _ _ _ _ = Nothing

type family TryElimEq (premise :: Type) (goal :: Type) config (subgoals :: [Maybe Node]) where

    TryElimEq (x :=: y) goal config '[Nothing] = Nothing

    TryElimEq (x :=: y) goal config '[] =
        TryElimEq (x :=: y) goal (Unassume (x :=: y) config) '[TryInfer Find (x :=: y) config Nothing]

    TryElimEq (x :=: y) goal config '[Just node_eq] =
        TryElimEq (x :=: y) goal config '[Just node_eq, TryInfer Search (Substitute goal x y) config Nothing]

    TryElimEq (x :=: y) goal config '[Just node_eq, Just node_pred] =
        Just (ElimPredicate (Predicate goal x x) (ElimEq (x :=: y) node_eq (IntroPredicate node_pred)))

    TryElimEq (x :=: y) goal config '[Just node_eq, Nothing] =
        TryElimEq (x :=: y) goal config '[Just node_eq, Nothing, TryInfer Search (Substitute goal y x) config Nothing]

    TryElimEq (x :=: y) goal config '[Just node_eq, Nothing, Just node_pred] =
        Just (ElimPredicate (Predicate goal y y) (ElimEq (y :=: x) (Symmetry node_eq) (IntroPredicate node_pred)))

    TryElimEq (x :=: y) goal config '[Just node_eq, Nothing, Nothing] = Nothing

type family TryElimForall (candidate :: Type) (premise :: Type) (goal :: Type) config match (subgoals :: [Maybe Node]) where

    TryElimForall _ _ _ _ _ '[Nothing] = Nothing

    TryElimForall _ _ _ _ _ '[_, Just node] = Just node

    TryElimForall candidate (Forall x a p) goal config True '[Just node] =
        Just (ElimPredicate (Predicate p x candidate) (ElimForall node))

    TryElimForall (X n) (Forall x a p) goal config False '[Just node] =
        TryElimForall (X n) (Forall x a p) goal config False '[Just node, TryElimPremise (Substitute p x (X n)) goal config '[]]

    TryElimForall (X Z) (Forall x a p) goal config False '[Just node, Nothing] = Nothing

    TryElimForall (X (S n)) (Forall x a p) goal config False '[Just node, Nothing] =
        TryElimForall (X n) (Forall x a p) goal config (Equal goal (Substitute p x (X n))) '[Just node]


type family TryElimPred (premise :: Type) (goal :: Type) config match (subgoal :: [Maybe Node]) where

    TryElimPred _ _ _ False _ = Nothing
    TryElimPred _ _ _ _ '[Nothing] = Nothing

    TryElimPred (Predicate p x t) goal config True '[] =
        TryElimPred (Predicate p x t) goal config True '[TryInfer Find (Predicate p x t) config Nothing]

    TryElimPred (Predicate p x t) goal config True '[Just node] =
        Just (ElimPredicate (Predicate p x t) node)
