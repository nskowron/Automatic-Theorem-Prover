{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}

module Search where

import Proposition
import Node
import HSet

import Data.Kind (Type)
import Control.Applicative ( (<|>) )


-- move to utils later --
type family a :<|>: b where
    Just a :<|>: _ = Just a
    Nothing :<|>: b = b

type family f :<$>: a where
    _ :<$>: Nothing = Nothing
    f :<$>: Just a = Just (f a)

type family f :<*>: a where
    Nothing :<*>: _ = Nothing
    _ :<*>: Nothing = Nothing
    Just f :<*>: Just a = Just (f a)

type family Member a l where
    Member a '[] = False
    Member a (a ': l) = True
    Member a (l ': ls) = Member a ls

type family If p a b where
    If True a _ = a
    If False _ b = b

type family FromMaybe d a where
    FromMaybe d Nothing = d
    FromMaybe _ (Just a) = a
--------------------------


data Mode = Search | Find

type family SearchNode (context :: [Type]) (conclusion :: Type) (parents :: [([Type], Type)]) (mode :: Mode) :: Maybe Node where

    SearchNode context conclusion parents mode =
        ActualSearchNode context conclusion (Insert '(context, conclusion) parents) mode (Member '(context, conclusion) parents)

type family ActualSearchNode (context :: [Type]) (conclusion :: Type) (parents :: [([Type], Type)]) (mode :: Mode) repeated :: Maybe Node where

    ActualSearchNode context conclusion parents Search False =
        TryIntro context conclusion (Insert '(context, conclusion) parents)
            :<|>: IterNodes context conclusion context (Insert '(context, conclusion) parents) Search

    ActualSearchNode context conclusion parents Find False = 
        IterNodes context conclusion context (Insert '(context, conclusion) parents) Find


type family IterNodes (context :: [Type]) (conclusion :: Type) (premises :: [Type]) (parents :: [([Type], Type)]) (mode :: Mode) :: Maybe Node where

    IterNodes context conclusion (conclusion ': premises) parents mode =
        Just Project

    IterNodes context conclusion (premise ': premises) parents mode =
        TryElim context conclusion premise parents mode
            :<|>: IterNodes context conclusion premises parents mode

    IterNodes _ _ _ _ _ = Nothing


type family TryIntro (context :: [Type]) (conclusion :: Type) (parents :: [([Type], Type)]) :: Maybe Node where

    TryIntro _ () _ = Just IntroTrue

    TryIntro context (a -> b) parents =
        IntroImpl
            :<$>: SearchNode (Insert a context) b parents Search

    TryIntro context (a `And` b) parents =
        IntroAnd
            :<$>: SearchNode context a parents Search
            :<*>: SearchNode context b parents Search

    TryIntro context (a `Or` b) parents =
        ( IntroOrLeft
            :<$>: SearchNode context a parents Search
        ) :<|>: ( IntroOrRight
            :<$>: SearchNode context b parents Search
        )

    TryIntro _ _ _ = Nothing

    
type family TryElim (context :: [Type]) (conclusion :: Type) (premise :: Type) (parents :: [([Type], Type)]) (mode :: Mode) :: Maybe Node where

    TryElim context b (a -> b) parents mode =
        ElimImpl (a -> b)
            :<$>: SearchNode context (a -> b) parents Find
            :<*>: SearchNode context a parents Search

    TryElim context c (a -> b) parents mode =
        TryElim context c b parents mode

    TryElim context a (a `And` b) parents mode =
        ElimAndLeft (a `And` b)
            :<$>: SearchNode context (a `And` b) parents Find

    TryElim context b (a `And` b) parents mode =
        ElimAndRight (a `And` b)
            :<$>: SearchNode context (a `And` b) parents Find

    TryElim context c (a `And` b) parents mode =
        TryElim context c a parents mode
            :<|>: TryElim context c b parents mode

    TryElim context c (a `Or` b) parents Search =
        ElimOr (a `Or` b)
            :<$>: SearchNode context (a `Or` b) parents Find
            :<*>: SearchNode (Insert a context) c parents Search
            :<*>: SearchNode (Insert b context) c parents Search

    TryElim _ _ _ _ _ = Nothing
