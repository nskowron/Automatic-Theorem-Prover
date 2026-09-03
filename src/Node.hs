module Node where

import Utils
import Proposition

import Data.HList ( HList(..), hHead, hTail )
import Data.Kind ( Type )
import Data.Void ( absurd )


-- === Node === --
data Node = Unprovable

    | Project

    | IntroTrue
    | IntroImpl Node
    | IntroAnd Node Node
    | IntroOrLeft Node
    | IntroOrRight Node

    | ElimFalse Node
    | ElimImpl Type Node Node
    | ElimAndLeft Type Node
    | ElimAndRight Type Node
    | ElimOr Type Node Node Node


-- === Inferable === --
class Inferable (node :: Node) (context :: [Type]) (conclusion :: Type) where
    infer :: HList context -> conclusion


-- === Project === --
instance {-# OVERLAPPING #-}
    Inferable Project (conclusion ': context) conclusion where
    infer = hHead

instance {-# OVERLAPPABLE #-}
    ( Inferable Project context conclusion
    ) => Inferable Project (premise ': context) conclusion where
    infer = infer @Project @context @conclusion . hTail


-- === Intro === --
instance Inferable IntroTrue context True where
    infer _ = ()

instance
    ( Inferable node (a ': context) b
    ) => Inferable (IntroImpl node) context (a -> b) where
    infer ctxt = \x -> infer @node @(a ': context) @b (HCons x ctxt)

instance 
    ( Inferable node_left context a
    , Inferable node_right context b
    ) => Inferable (IntroAnd node_left node_right) context (a `And` b) where
    infer ctxt = (infer @node_left @context @a ctxt, infer @node_right @context @b ctxt)

instance
    ( Inferable node context a
    ) => Inferable (IntroOrLeft node) context (a `Or` b) where
    infer ctxt = Left $ infer @node @context @a ctxt

instance
    ( Inferable node context b
    ) => Inferable (IntroOrRight node) context (a `Or` b) where
    infer ctxt = Right $ infer @node @context @b ctxt


-- === Elim === --
instance
    ( Inferable node context False
    ) => Inferable (ElimFalse node) context a where
    infer ctxt = absurd $ infer @node @context @False ctxt :: a

instance
    ( Inferable node_impl context (a -> b)
    , Inferable node_arg context a
    ) => Inferable (ElimImpl (a -> b) node_impl node_arg) context b where
    infer ctxt = infer @node_impl @context @(a -> b) ctxt $ infer @node_arg @context @a ctxt

instance
    ( Inferable node context (a `And` b)
    ) => Inferable (ElimAndLeft (a `And` b) node) context a where
    infer ctxt = fst $ infer @node @context @(a `And` b) ctxt

instance
    ( Inferable node context (a `And` b)
    ) => Inferable (ElimAndRight (a `And` b) node) context b where
    infer ctxt = snd $ infer @node @context @(a `And` b) ctxt

instance
    ( Inferable node_or context (a `Or` b)
    , Inferable node_left (a ': context) c
    , Inferable node_right (b ': context) c
    ) => Inferable (ElimOr (a `Or` b) node_or node_left node_right) context c where
    infer ctxt = case infer @node_or @context @(a `Or` b) ctxt of
        Left x -> infer @node_left @(a ': context) @c (HCons x ctxt)
        Right y -> infer @node_right @(b ': context) @c (HCons y ctxt)


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
