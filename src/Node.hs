module Node where

import Utils
import Proposition
import FOL

import Data.HList ( HList(..), hHead, hTail )
import Data.Kind ( Type )
import Data.Proxy ( Proxy(..) )
import Data.Type.Equality ( (:~:)(..) )
import Data.Void ( absurd )
import GHC.TypeLits ( Symbol )
import Unsafe.Coerce ( unsafeCoerce )


-- === Node === --
data Node where
    Unprovable :: Node

    Project :: Node

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
    ElimEq :: a -> p -> Node -> Node -> Node

    IntroPred :: Node -> Node
    IntroForall :: Node -> Node
    IntroExists :: a -> Node -> Node

    Induction :: Node -> Node -> Node


-- === Inferable === --
class Inferable (node :: Node) (context :: [Type]) (env :: [(Symbol, Type)]) (conclusion :: Type) where
    infer :: HList context -> conclusion


-- === Project === --
instance {-# OVERLAPPING #-}
    Inferable Project (conclusion ': context) env conclusion where
    infer = hHead

instance {-# OVERLAPPABLE #-}
    ( Inferable Project context env conclusion
    ) => Inferable Project (premise ': context) env conclusion where
    infer = infer @Project @context @env @conclusion . hTail


-- === Intro === --
instance Inferable IntroTrue context env True where
    infer _ = ()

instance
    ( Inferable node (a ': context) env b
    ) => Inferable (IntroImpl node) context env (a -> b) where
    infer ctxt = \x -> infer @node @(a ': context) @env @b (HCons x ctxt)

instance 
    ( Inferable node_left context env a
    , Inferable node_right context env b
    ) => Inferable (IntroAnd node_left node_right) context env (a `And` b) where
    infer ctxt = (infer @node_left @context @env @a ctxt, infer @node_right @context @env @b ctxt)

instance
    ( Inferable node context env a
    ) => Inferable (IntroOrLeft node) context env (a `Or` b) where
    infer ctxt = Left $ infer @node @context @env @a ctxt

instance
    ( Inferable node context env b
    ) => Inferable (IntroOrRight node) context env (a `Or` b) where
    infer ctxt = Right $ infer @node @context @env @b ctxt


-- === Elim === --
instance
    ( Inferable node context env False
    ) => Inferable (ElimFalse node) context env a where
    infer ctxt = absurd $ infer @node @context @env @False ctxt :: a

instance
    ( (a -> b) ~ Apply (raw_a -> raw_b) env
    , Inferable node_impl context env (a -> b)
    , Inferable node_arg context env a
    ) => Inferable (ElimImpl (raw_a -> raw_b) node_impl node_arg) context env b where
    infer ctxt = infer @node_impl @context @env @(a -> b) ctxt $ infer @node_arg @context @env @a ctxt

instance
    ( (a `And` b) ~ Apply (raw_a `And` raw_b) env
    , Inferable node context env (a `And` b)
    ) => Inferable (ElimAndLeft (raw_a `And` raw_b) node) context env a where
    infer ctxt = fst $ infer @node @context @env @(a `And` b) ctxt

instance
    ( (a `And` b) ~ Apply (raw_a `And` raw_b) env
    , Inferable node context env (a `And` b)
    ) => Inferable (ElimAndRight (raw_a `And` raw_b) node) context env b where
    infer ctxt = snd $ infer @node @context @env @(a `And` b) ctxt

instance
    ( (a `Or` b) ~ Apply (raw_a `Or` raw_b) env
    , Inferable node_or context env (a `Or` b)
    , Inferable node_left (a ': context) env c
    , Inferable node_right (b ': context) env c
    ) => Inferable (ElimOr (raw_a `Or` raw_b) node_or node_left node_right) context env c where
    infer ctxt = case infer @node_or @context @env @(a `Or` b) ctxt of
        Left x -> infer @node_left @(a ': context) @env @c (HCons x ctxt)
        Right y -> infer @node_right @(b ': context) @env @c (HCons y ctxt)


-- === FOL === --
instance
    Inferable Reflexivity context env (a :~: a) where
    infer _ = Refl

instance
    ( Inferable node context env (b :=: a)
    ) => Inferable (Symmetry node) context env (a :=: b) where
    infer ctxt = case infer @node @context @env @(b :=: a) ctxt of
        Refl -> Refl

instance
    ( (x :=: y) ~ Apply (raw_x :=: raw_y) env
    , py ~ Apply raw_py env
    , px ~ Apply (Replace raw_py raw_y raw_x) env
    , Inferable node_eq context env (x :=: y)
    , Inferable node_pred context env px
    ) => Inferable (ElimEq (raw_x :=: raw_y) raw_py node_eq node_pred) context env py where
    infer ctxt = case infer @node_eq @context @env @(x :=: y) ctxt of
        Refl -> unsafeCoerce $ infer @node_pred @context @env @px ctxt

instance
    ( Inferable node context ('(x, v) ': env) (Eval (Apply p '[ '(x, v)]))
    ) => Inferable (IntroPred node) context env (Predicate p x v) where
    infer ctxt = Predicate $ infer @node @context @('(x, v) ': env) @(Eval (Apply p '[ '(x, v)])) ctxt

instance
    ( forall (v :: d). Inferable (IntroPred node) context env (Predicate p x (a v))
    ) => Inferable (IntroForall node) context env (Forall x (a :: d -> Type) p) where
    infer ctxt = Forall $ infer @(IntroPred node) @context @env ctxt

instance
    ( Inferable (IntroPred node) context env (Predicate p x (a v))
    ) => Inferable (IntroExists (v :: d) node) context env (Exists x (a :: d -> Type) p) where
    infer ctxt = Exists $ infer @(IntroPred node) @context @env @(Predicate p x (a v)) ctxt


-- === ShowType === --
class ShowNode (node :: Node) (context :: [Type]) (conclusion :: Type) where
    showNode :: Int -> String

instance 
    ( ShowNode node '[] conclusion
    ) => ShowType ('(node, conclusion) :: (Node, Type)) where
    showType = showNode @node @'[] @conclusion 0


-- === Unprovable === --
instance
    ShowNode Unprovable context conclusion where
    showNode _ = "..."


-- === Project === --
instance {-# OVERLAPPING #-}
    ShowNode Project (conclusion ': context) conclusion where
    showNode x = "x" ++ show x

instance {-# OVERLAPPABLE #-}
    ( ShowNode Project context conclusion
    ) => ShowNode Project (premise ': context) conclusion where
    showNode x = showNode @Project @context @conclusion (x - 1)


-- === Intro === --
instance ShowNode IntroTrue context True where
    showNode _ = "True"

instance
    ( ShowNode node (a ': context) b
    ) => ShowNode (IntroImpl node) context (a -> b) where
    showNode x = "\\x" ++ show (x + 1) ++ " -> " ++ showNode @node @(a ': context) @b (x + 1)

instance 
    ( ShowNode node_left context a
    , ShowNode node_right context b
    ) => ShowNode (IntroAnd node_left node_right) context (a `And` b) where
    showNode x = "(" ++ showNode @node_left @context @a x ++ ", " ++ showNode @node_right @context @b x ++ ")"

instance
    ( ShowNode node context a
    ) => ShowNode (IntroOrLeft node) context (a `Or` b) where
    showNode x = "Left (" ++ showNode @node @context @a x ++ ")"

instance
    ( ShowNode node context b
    ) => ShowNode (IntroOrRight node) context (a `Or` b) where
    showNode x = "Right (" ++ showNode @node @context @b x ++ ")"


-- === Elim === --
instance
    ( ShowNode node context False
    ) => ShowNode (ElimFalse node) context a where
    showNode x = "absurd (" ++ showNode @node @context @False x ++ ")"

instance
    ( ShowNode node_impl context (a -> b)
    , ShowNode node_arg context a
    ) => ShowNode (ElimImpl (a -> b) node_impl node_arg) context b where
    showNode x = showNode @node_impl @context @(a -> b) x ++ " (" ++ showNode @node_arg @context @a x ++ ")"

instance
    ( ShowNode node context (a `And` b)
    ) => ShowNode (ElimAndLeft (a `And` b) node) context a where
    showNode x = "fst (" ++ showNode @node @context @(a `And` b) x ++ ")"

instance
    ( ShowNode node context (a `And` b)
    ) => ShowNode (ElimAndRight (a `And` b) node) context b where
    showNode x = "snd (" ++ showNode @node @context @(a `And` b) x ++ ")"

instance
    ( ShowNode node_or context (a `Or` b)
    , ShowNode node_left (a ': context) c
    , ShowNode node_right (b ': context) c
    ) => ShowNode (ElimOr (a `Or` b) node_or node_left node_right) context c where
    showNode x = "case " ++ showNode @node_or @context @(a `Or` b) x ++ " of { " ++
        "Left x" ++ show (x + 1) ++ " -> " ++ showNode @node_left @(a ': context) @c (x + 1) ++ "; " ++
        "Right x" ++ show (x + 1) ++ " -> " ++ showNode @node_right @(b ': context) @c (x + 1) ++ " }"


-- === FOL === --
instance
    ShowNode Reflexivity context (a :~: a) where
    showNode _ = "Refl"

-- instance
--     ( forall (v :: a). ShowNode node context (Eval p x v)
--     ) => ShowNode (IntroForall node) context (Forall x a p) where
--     showNode x = "Forall (" ++ showNode @node @context x ++ ")"

-- instance
--     ( ShowNode node context (Eval p x v)
--     ) => ShowNode (IntroExists (v :: a) node) context (Exists x a p) where
--     showNode x = "Exists (" ++ showNode @node @context @(Eval p x v) x ++ ")"
