{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}

module Node where

import Utils
import Proposition

import Data.HList ( HList(..), hHead, hTail )
import Data.Kind ( Type )
import Data.Void ( absurd )


-- === Node === --
data Node = Unprovable

    | Project Type

    | IntroTrue
    | IntroImpl Node
    | IntroAnd Node Node
    | IntroOrLeft Node
    | IntroOrRight Node

    | ElimFalse Node
    | ElimImpl Node Node
    | ElimAndLeft Node
    | ElimAndRight Node
    | ElimOr Node Node Node


-- === Inferable === --
class Inferable (node :: Node) (context :: [Type]) where
    infer :: HList context -> conclusion


-- === Project === --
instance {-# OVERLAPPING #-}
    Inferable ('Project :: Node a) (a ': context) where
    infer = hHead

instance {-# OVERLAPPABLE #-}
    ( Inferable ('Project :: Node a) context
    ) => Inferable ('Project :: Node a) (premise ': context) where
    infer = infer @('Project :: Node a) @context . hTail


-- === Intro === --
instance Inferable IntroTrue context where
    infer _ = ()

instance
    ( Inferable node (a ': context)
    ) => Inferable (IntroImpl node) context where
    infer ctxt = \x -> infer @node @(a ': context) (HCons x ctxt)

instance 
    ( Inferable node_left context
    , Inferable node_right context
    ) => Inferable (IntroAnd node_left node_right) context where
    infer ctxt = (infer @node_left @context ctxt, infer @node_right @context ctxt)

instance
    ( Inferable node context
    ) => Inferable (IntroOrLeft node) context where
    infer ctxt = Left $ infer @node @context ctxt

instance
    ( Inferable node context
    ) => Inferable (IntroOrRight node) context where
    infer ctxt = Right $ infer @node @context ctxt


-- === Elim === --
instance
    ( Inferable node context
    ) => Inferable (ElimFalse node) context where
    infer ctxt = absurd $ infer @node @context ctxt

instance
    ( Inferable node_impl context
    , Inferable node_arg context
    ) => Inferable (ElimImpl node_impl node_arg) context where
    infer ctxt = infer @node_impl @context ctxt $ infer @node_arg @context ctxt

instance
    ( Inferable node context
    ) => Inferable (ElimAndLeft node) context where
    infer ctxt = fst $ infer @node @context ctxt

instance
    ( Inferable node context
    ) => Inferable (ElimAndRight node) context where
    infer ctxt = snd $ infer @node @context ctxt

instance
    ( Inferable node_or context
    , Inferable node_left (a ': context)
    , Inferable node_right (b ': context)
    ) => Inferable (ElimOr node_or node_left node_right) context where
    infer ctxt = case infer @node_or @context ctxt of
        Left x -> infer @node_left @(a ': context) (HCons x ctxt)
        Right y -> infer @node_right @(b ': context) (HCons y ctxt)


-- === ShowType === --
class ShowNode (node :: Node conclusion) (context :: [Type]) where
    showNode :: Int -> String

instance 
    ( ShowNode node '[]
    ) => ShowType (node :: Node conclusion) where
    showType = showNode @node @'[] 0


-- === Unprovable === --
instance
    ShowNode Unprovable context where
    showNode _ = "..."


-- === Project === --
instance {-# OVERLAPPING #-}
    ShowNode (Project :: Node a) (a ': context) where
    showNode x = "x" ++ show x

instance {-# OVERLAPPABLE #-}
    ( ShowNode (Project :: Node a) context
    ) => ShowNode (Project :: Node a) (premise ': context) where
    showNode x = showNode @(Project :: Node a) @context (x - 1)


-- === Intro === --
instance ShowNode IntroTrue context where
    showNode _ = "True"

instance
    ( ShowNode node (a ': context)
    ) => ShowNode (IntroImpl node) context where
    showNode x = "\\x" ++ show (x + 1) ++ " -> " ++ showNode @node @(a ': context) (x + 1)

instance 
    ( ShowNode node_left context
    , ShowNode node_right context
    ) => ShowNode (IntroAnd node_left node_right) context where
    showNode x = "(" ++ showNode @node_left @context x ++ ", " ++ showNode @node_right @context x ++ ")"

instance
    ( ShowNode node context
    ) => ShowNode (IntroOrLeft node) context where
    showNode x = "Left (" ++ showNode @node @context x ++ ")"

instance
    ( ShowNode node context
    ) => ShowNode (IntroOrRight node) context where
    showNode x = "Right (" ++ showNode @node @context x ++ ")"


-- === Elim === --
instance
    ( ShowNode node context
    ) => ShowNode (ElimFalse node) context where
    showNode x = "absurd (" ++ showNode @node @context @False x ++ ")"

instance
    ( ShowNode node_impl context
    , ShowNode node_arg context
    ) => ShowNode (ElimImpl node_impl node_arg) context where
    showNode x = showNode @node_impl @context x ++ " (" ++ showNode @node_arg @context x ++ ")"

instance
    ( ShowNode node context
    ) => ShowNode (ElimAndLeft node) context where
    showNode x = "fst (" ++ showNode @node @context x ++ ")"

instance
    ( ShowNode node context
    ) => ShowNode (ElimAndRight node) context where
    showNode x = "snd (" ++ showNode @node @context x ++ ")"

instance
    ( ShowNode node_or context
    , ShowNode node_left (a ': context)
    , ShowNode node_right (b ': context)
    ) => ShowNode (ElimOr node_or node_left node_right :: Node c) context where
    showNode x = "case " ++ showNode @(node_or :: Node (a `Or` b)) @context x ++ " of { " ++
        "Left x" ++ show (x + 1) ++ " -> " ++ showNode @node_left @(a ': context) (x + 1) ++ "; " ++
        "Right x" ++ show (x + 1) ++ " -> " ++ showNode @node_right @(b ': context) (x + 1) ++ " }"
