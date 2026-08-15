{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DataKinds #-}

module Node where

import Proposition
import Utils

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
    emit :: Int -> String


-- === Project === --
instance {-# OVERLAPPING #-}
    Inferable Project (conclusion ': context) conclusion where
    infer = hHead
    emit x = "x" ++ show x

instance {-# OVERLAPPABLE #-}
    ( Inferable Project context conclusion
    ) => Inferable Project (premise ': context) conclusion where
    infer = infer @Project @context @conclusion . hTail
    emit x = emit @Project @context @conclusion (x - 1)


-- === Intro === --
instance Inferable IntroTrue context True where
    infer _ = ()
    emit _ = "True"

instance
    ( Inferable node (a ': context) b
    ) => Inferable (IntroImpl node) context (a -> b) where
    infer ctxt = \x -> infer @node @(a ': context) @b (HCons x ctxt)
    emit x = "\\x" ++ show (x + 1) ++ " -> " ++ emit @node @(a ': context) @b (x + 1)

instance 
    ( Inferable node_left context a
    , Inferable node_right context b
    ) => Inferable (IntroAnd node_left node_right) context (a `And` b) where
    infer ctxt = (infer @node_left @context @a ctxt, infer @node_right @context @b ctxt)
    emit x = "(" ++ emit @node_left @context @a x ++ ", " ++ emit @node_right @context @b x ++ ")"

instance
    ( Inferable node context a
    ) => Inferable (IntroOrLeft node) context (a `Or` b) where
    infer ctxt = Left $ infer @node @context @a ctxt
    emit x = "Left $ " ++ emit @node @context @a x

instance
    ( Inferable node context b
    ) => Inferable (IntroOrRight node) context (a `Or` b) where
    infer ctxt = Right $ infer @node @context @b ctxt
    emit x = "Right $ " ++ emit @node @context @b x


-- === Elim === --
instance
    ( Inferable node context False
    ) => Inferable (ElimFalse node) context a where
    infer ctxt = absurd $ infer @node @context @False ctxt :: a
    emit x = "absurd $ " ++ emit @node @context @False x

instance
    ( Inferable node_impl context (a -> b)
    , Inferable node_arg context a
    ) => Inferable (ElimImpl (a -> b) node_impl node_arg) context b where
    infer ctxt = infer @node_impl @context @(a -> b) ctxt $ infer @node_arg @context @a ctxt
    emit x = emit @node_impl @context @(a -> b) x ++ " $ " ++ emit @node_arg @context @a x

instance
    ( Inferable node context (a `And` b)
    ) => Inferable (ElimAndLeft (a `And` b) node) context a where
    infer ctxt = fst $ infer @node @context @(a `And` b) ctxt
    emit x = "fst $ " ++ emit @node @context @(a `And` b) x

instance
    ( Inferable node context (a `And` b)
    ) => Inferable (ElimAndRight (a `And` b) node) context b where
    infer ctxt = snd $ infer @node @context @(a `And` b) ctxt
    emit x = "snd $ " ++ emit @node @context @(a `And` b) x

instance
    ( Inferable node_or context (a `Or` b)
    , Inferable node_left (a ': context) c
    , Inferable node_right (b ': context) c
    ) => Inferable (ElimOr (a `Or` b) node_or node_left node_right) context c where
    infer ctxt = case infer @node_or @context @(a `Or` b) ctxt of
        Left x -> infer @node_left @(a ': context) @c (HCons x ctxt)
        Right y -> infer @node_right @(b ': context) @c (HCons y ctxt)
    emit x = "case " ++ emit @node_or @context @(a `Or` b) x ++ " of { " ++
        "Left x" ++ show (x + 1) ++ " -> " ++ emit @node_left @(a ': context) @c (x + 1) ++ "; " ++
        "Right x" ++ show (x + 1) ++ " -> " ++ emit @node_right @(b ': context) @c (x + 1) ++ " }"
