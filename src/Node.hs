module Node where

import SearchUtils
import Utils
import Proposition
import FOL

import Data.HList ( HList(..), hHead, hTail )
import Data.Kind ( Type )
import Data.Proxy ( Proxy(..) )
import Data.Type.Equality ( (:~:)(..) )
import Data.Void ( absurd )
import Data.Type.Nat


-- === Node === --
data Node where
    Unprovable :: Node

    Project :: Nat -> Node

    IntroTrue :: Node
    IntroImpl :: Node -> Node
    IntroAnd :: Node -> Node -> Node
    IntroOrLeft :: Node -> Node
    IntroOrRight :: Node -> Node

    ElimFalse :: Node -> Node
    ElimImpl :: a -> Node -> Node -> Node
    ElimAndLeft :: a -> Node -> Node
    ElimAndRight :: a -> Node -> Node
    ElimOr :: a -> Node -> Node -> Node -> Node

    Reflexivity :: Node
    Symmetry :: Node -> Node
    ElimEq :: a -> Node -> Node -> Node

    IntroPredicate :: Node -> Node
    IntroForall :: Node -> Node
    IntroExists :: a -> Node -> Node

    ElimPredicate :: a -> Node -> Node
    ElimPredicateContext :: a -> Node -> Node -> Node
    ElimForall :: Node -> Node
    ElimExists :: a -> Node -> Node -> Node


-- === Inferable === --
class Inferable (node :: Node) (env :: [(Type, Type)]) (context :: [Type]) (conclusion :: Type) where
    infer :: HList context -> conclusion


-- === Project === --
instance
    Inferable (Project Z) env (conclusion ': context) conclusion where
    infer = hHead

instance
    ( Inferable (Project n) env context conclusion
    ) => Inferable (Project (S n)) env (premise ': context) conclusion where
    infer = infer @(Project n) @env @context @conclusion . hTail


-- instance {-# OVERLAPPABLE #-}
--     Inferable Project env (Predicate p x t ': context) (Predicate p x s) where


-- === Intro === --
instance Inferable IntroTrue env context True where
    infer _ = ()

instance
    ( Inferable node env (a ': context) b
    ) => Inferable (IntroImpl node) env context (a -> b) where
    infer ctxt = \x -> infer @node @env @(a ': context) @b (HCons x ctxt)

instance 
    ( Inferable node_left env context a
    , Inferable node_right env context b
    ) => Inferable (IntroAnd node_left node_right) env context (a `And` b) where
    infer ctxt = (infer @node_left @env @context @a ctxt, infer @node_right @env @context @b ctxt)

instance
    ( Inferable node env context a
    ) => Inferable (IntroOrLeft node) env context (a `Or` b) where
    infer ctxt = Left $ infer @node @env @context @a ctxt

instance
    ( Inferable node env context b
    ) => Inferable (IntroOrRight node) env context (a `Or` b) where
    infer ctxt = Right $ infer @node @env @context @b ctxt


-- === Elim === --
instance
    ( Inferable node env context False
    ) => Inferable (ElimFalse node) env context a where
    infer ctxt = absurd $ infer @node @env @context @False ctxt

instance
    ( (a -> b) ~ Apply type_impl env
    , Inferable node_impl env context (a -> b)
    , Inferable node_arg env context a
    ) => Inferable (ElimImpl type_impl node_impl node_arg) env context b where
    infer ctxt = infer @node_impl @env @context @(a -> b) ctxt $ infer @node_arg @env @context @a ctxt

instance
    ( (a `And` b) ~ Apply type_and env
    , Inferable node env context (a `And` b)
    ) => Inferable (ElimAndLeft type_and node) env context a where
    infer ctxt = fst $ infer @node @env @context @(a `And` b) ctxt

instance
    ( (a `And` b) ~ Apply type_and env
    , Inferable node env context (a `And` b)
    ) => Inferable (ElimAndRight type_and node) env context b where
    infer ctxt = snd $ infer @node @env @context @(a `And` b) ctxt

instance
    ( (a `Or` b) ~ Apply type_or env
    , Inferable node_or env context (a `Or` b)
    , Inferable node_left env (a ': context) c
    , Inferable node_right env (b ': context) c
    ) => Inferable (ElimOr type_or node_or node_left node_right) env context c where
    infer ctxt = case infer @node_or @env @context @(a `Or` b) ctxt of
        Left x -> infer @node_left @env @(a ': context) @c (HCons x ctxt)
        Right y -> infer @node_right @env @(b ': context) @c (HCons y ctxt)


-- -- === FOL === --
instance
    Inferable Reflexivity env context (x :=: x) where
    infer _ = Refl

instance
    ( Inferable node env context (y :=: x)
    ) => Inferable (Symmetry node) env context (x :=: y) where
    infer ctxt = case infer @node @env @context @(y :=: x) ctxt of
        Refl -> Refl

instance
    ( (x :=: y) ~ Apply type_eq env
    , Inferable node_eq env context (x :=: y)
    , Inferable node_pred env context (Predicate p a y)
    ) => Inferable (ElimEq type_eq node_eq node_pred) env context (Predicate p a x) where
    infer ctxt = case infer @node_eq @env @context @(x :=: y) ctxt of
        Refl -> infer @node_pred @env @context @(Predicate p a y) ctxt

instance
    ( Inferable node (Map x t env) context (Substitute p x t)
    ) => Inferable (IntroPredicate node) env context (Predicate p x t) where
    infer ctxt = Predicate $ infer @node @(Map x t env) @context @(Substitute p x t) ctxt

instance
    ( forall t. Inferable node ('(X (S n), x) ': '(X n, s) ': env) context (Predicate p x (a t))
    ) => Inferable (IntroForall node) ('(X n, s) ': env) context (Forall x a p) where
    infer ctxt = Forall $ infer @node @('(X (S n), x) ': '(X n, s) ': env) @context ctxt

instance
    ( a t ~ Apply type_witness env
    , Inferable node env context (Predicate p x (a t))
    ) => Inferable (IntroExists type_witness node) env context (Exists x a p) where
    infer ctxt = Exists $ infer @node @env @context @(Predicate p x (a t)) ctxt

instance
    ( Predicate p x t ~ Apply type_pred env
    , Substitute p x t ~ pt
    , Inferable node env context (Predicate p x t)
    ) => Inferable (ElimPredicate type_pred node) env context pt where
    infer ctxt = case infer @node @env @context @(Predicate p x t) ctxt of
        (Predicate p) -> p

instance
    ( Predicate p x t ~ Apply type_pred env
    , Inferable node_pred env context (Predicate p x t)
    , Inferable node_pt (Map x t env) (Substitute p x t ': context) pt
    ) => Inferable (ElimPredicateContext type_pred node_pred node_pt) env context pt where
    infer ctxt = case infer @node_pred @env @context @(Predicate p x t) ctxt of
        (Predicate p) -> infer @node_pt @(Map x t env) @(Substitute p x t ': context) @pt (HCons p ctxt)

instance
    ( Inferable node env context (Forall x a p)
    ) => Inferable (ElimForall node) env context (Predicate p x (a t)) where
    infer ctxt = case infer @node @env @context @(Forall x a p) ctxt of
        (Forall p) -> p

instance
    ( Exists x a p ~ Apply type_exists ('(X n, s) ': env)
    , Inferable node_exists ('(X n, s) ': env) context (Exists x a p)
    , forall t. Inferable node_c ('(X (S n), x) ': '(X n, s) ': env) (Predicate p x (a t) ': context) c
    ) => Inferable (ElimExists type_exists node_exists node_c) ('(X n, s) ': env) context c where
    infer ctxt = case infer @node_exists @('(X n, s) ': env) @context @(Exists x a p) ctxt of
        (Exists p) -> infer @node_c @('(X (S n), x) ': '(X n, s) ': env) (HCons p ctxt)


-- === ShowType === --
class ShowNode (node :: Node) (var :: Nat) (context :: [Type]) (conclusion :: Type) where
    showNode :: Int -> String

instance 
    ( ShowNode node Z '[] conclusion
    ) => ShowType ('(node, conclusion) :: (Node, Type)) where
    showType = showNode @node @Z @'[] @conclusion 0


-- === Unprovable === --
instance
    ShowNode Unprovable n context conclusion where
    showNode _ = "..."


-- === Project === --
instance
    ShowNode (Project Z) n (conclusion ': context) conclusion where
    showNode x = "x" ++ show x

instance
    ( ShowNode (Project x) n context conclusion
    ) => ShowNode (Project (S x)) n (premise ': context) conclusion where
    showNode x = showNode @(Project x) @n @context @conclusion (x - 1)


-- === Intro === --
instance ShowNode IntroTrue n context True where
    showNode _ = "True"

instance
    ( ShowNode node n (a ': context) b
    ) => ShowNode (IntroImpl node) n context (a -> b) where
    showNode x = "\\x" ++ show (x + 1) ++ " -> " ++ showNode @node @n @(a ': context) @b (x + 1)

instance 
    ( ShowNode node_left n context a
    , ShowNode node_right n context b
    ) => ShowNode (IntroAnd node_left node_right) n context (a `And` b) where
    showNode x = "(" ++ showNode @node_left @n @context @a x ++ ", " ++ showNode @node_right @n @context @b x ++ ")"

instance
    ( ShowNode node n context a
    ) => ShowNode (IntroOrLeft node) n context (a `Or` b) where
    showNode x = "Left (" ++ showNode @node @n @context @a x ++ ")"

instance
    ( ShowNode node n context b
    ) => ShowNode (IntroOrRight node) n context (a `Or` b) where
    showNode x = "Right (" ++ showNode @node @n @context @b x ++ ")"


-- === Elim === --
instance
    ( ShowNode node n context False
    ) => ShowNode (ElimFalse node) n context a where
    showNode x = "absurd (" ++ showNode @node @n @context @False x ++ ")"

instance
    ( ShowNode node_impl n context (a -> b)
    , ShowNode node_arg n context a
    ) => ShowNode (ElimImpl (a -> b) node_impl node_arg) n context b where
    showNode x = showNode @node_impl @n @context @(a -> b) x ++ " (" ++ showNode @node_arg @n @context @a x ++ ")"

instance
    ( ShowNode node n context (a `And` b)
    ) => ShowNode (ElimAndLeft (a `And` b) node) n context a where
    showNode x = "fst (" ++ showNode @node @n @context @(a `And` b) x ++ ")"

instance
    ( ShowNode node n context (a `And` b)
    ) => ShowNode (ElimAndRight (a `And` b) node) n context b where
    showNode x = "snd (" ++ showNode @node @n @context @(a `And` b) x ++ ")"

instance
    ( ShowNode node_or n context (a `Or` b)
    , ShowNode node_left n (a ': context) c
    , ShowNode node_right n (b ': context) c
    ) => ShowNode (ElimOr (a `Or` b) node_or node_left node_right) n context c where
    showNode x = "case (" ++ showNode @node_or @n @context @(a `Or` b) x ++ ") of { " ++
        "Left x" ++ show (x + 1) ++ " -> " ++ showNode @node_left @n @(a ': context) @c (x + 1) ++ "; " ++
        "Right x" ++ show (x + 1) ++ " -> " ++ showNode @node_right @n @(b ': context) @c (x + 1) ++ " }"


-- === FOL === --
instance
    ShowNode Reflexivity n context (a :=: a) where
    showNode _ = "Refl"

instance
    ( ShowNode node n context (y :=: x)
    ) => ShowNode (Symmetry node) n context (x :=: y) where
    showNode x = "case (" ++ showNode @node @n @context @(y :=: x) x ++ ") of { " ++
        "Refl -> Refl }"

instance
    ( ShowNode node_eq n context (x :=: y)
    , ShowNode node_p n context (Substitute p y x)
    ) => ShowNode (ElimEq (x :=: y) node_eq node_p) n context p where
    showNode x = "case (" ++ showNode @node_eq @n @context @(x :=: y) x ++ ") of { " ++
        "Refl -> (" ++ showNode @node_p @n @context @(Substitute p y x) x ++ ") }"

instance
    ( ShowNode node n context (Substitute p x t)
    ) => ShowNode (IntroPredicate node) n context (Predicate p x t) where
    showNode x = "Predicate (" ++ showNode @node @n @context @(Substitute p x t) x ++ ")"

instance
    ( ShowNode node (S n) context (Predicate p x (X (S n)))
    ) => ShowNode (IntroForall node) n context (Forall x a p) where
    showNode x = "Forall (" ++ showNode @node @(S n) @context @(Predicate p x (X (S n))) x ++ ")"

-- instance
--     ( ShowNode node context (Substitute p (Var x) t)
--     ) => ShowNode (IntroExists t node) context (Exists x p) where
--     showNode x = "Exists (" ++ showNode @node @context @(Substitute p (Var x) t) x ++ ")"

-- instance
--     ( ShowNode node_exists context (Exists x p)
--     , ShowNode node_c (p ': context) c
--     ) => ShowNode (ElimExists (Exists x p) s node_exists node_c) context c where
--     showNode x = "case (" ++ showNode @node_exists @context @(Exists x p) x ++ ") of { " ++
--         "(Exists x" ++ show (x + 1) ++ ") -> (" ++ showNode @node_c @(p ': context) @c (x + 1) ++ ")"
