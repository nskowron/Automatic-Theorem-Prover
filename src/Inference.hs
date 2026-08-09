{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}

module Inference where

import Proposition
import HSet
import Utils ( Member, member )

import Control.Applicative ( (<|>) )
import Data.Kind ( Type )

import Prelude hiding ( Traversable, traverse )


-- === DECLARATIONS === --

-- search Algorithm --
class Deducible (conclusion :: Type) (context :: [Type]) (inferred :: [(Type, [Type])]) where
    deduce :: Maybe (HSet context -> conclusion)

class Inferable (conclusion :: Type) (context :: [Type]) (inferred :: [(Type, [Type])]) (candidates :: [(Type, [Type])]) where
    infer :: Maybe (HSet context -> conclusion)

data Find
data Match

class Traversable (conclusion :: Type) (premises :: [Type]) (context :: [Type]) (inferred :: [(Type, [Type])]) (mode :: Type) where
    traverse :: Maybe (HSet context -> conclusion)

class Matchable (conclusion :: Type) (premise :: Type) (context :: [Type]) (inferred :: [(Type, [Type])]) (mode :: Type) where
    match :: Maybe (HSet context -> conclusion)

-- Inference Rules --
class Projectable conclusion context where
    project :: Maybe (HSet context -> conclusion)

class Introducible conclusion context inferred where
    intro :: Maybe (HSet context -> conclusion)

class Eliminable conclusion premise context inferred where
    elim :: Maybe (HSet context -> conclusion)


-- === IMPLEMENTATION === --

-- Deducible --
instance
    ( Inferable conclusion context inferred inferred
    ) => Deducible conclusion context inferred where
    deduce = infer @conclusion @context @inferred @inferred

-- Inferable --
instance
    ( Introducible conclusion context (Insert '(conclusion, context) inferred)
    , Traversable conclusion context context (Insert '(conclusion, context) inferred) Match
    ) => Inferable conclusion context inferred '[] where
    infer = intro @conclusion @context @(Insert '(conclusion, context) inferred)
        <|> traverse @conclusion @context @context @(Insert '(conclusion, context) inferred) @Match

instance {-# OVERLAPPING #-}
    Inferable conclusion context inferred ('(conclusion, context) ': candidates) where
    infer = Nothing

instance {-# OVERLAPPABLE #-}
    ( Inferable conclusion context inferred candidates
    ) => Inferable conclusion context inferred (candidate ': candidates) where
    infer = infer @conclusion @context @inferred @candidates

-- Traversable --
instance
    Traversable conclusion '[] context inferred mode where
    traverse = Nothing

instance {-# OVERLAPPING #-}
    ( Projectable conclusion context
    ) => Traversable conclusion (conclusion ': premises) context inferred mode where
    traverse = project @conclusion @context

instance {-# OVERLAPPABLE #-}
    ( Member '(conclusion, premise) inferred
    , Matchable conclusion premise context inferred mode
    , Traversable conclusion premises context inferred mode
    ) => Traversable conclusion (premise ': premises) context inferred mode where
    traverse = match @conclusion @premise @context @inferred @mode
        <|> traverse @conclusion @premises @context @inferred @mode

-- Matchable --
instance {-# OVERLAPPING #-}
    ( Eliminable conclusion (a -> b) context inferred
    , Matchable conclusion b context inferred mode
    ) => Matchable conclusion (a -> b) context inferred mode where
    match = elim @conclusion @(a -> b) @context @inferred
        <|> match @conclusion @b @context @inferred @mode

instance {-# OVERLAPPING #-}
    ( Eliminable conclusion (a `And` b) context inferred
    , Matchable conclusion a context inferred mode
    , Matchable conclusion b context inferred mode
    ) => Matchable conclusion (a `And` b) context inferred mode where
    match = elim @conclusion @(a `And` b) @context @inferred
        <|> match @conclusion @a @context @inferred @mode
        <|> match @conclusion @b @context @inferred @mode

instance {-# OVERLAPPING #-}
    ( Eliminable conclusion (a `Or` b) context inferred
    ) => Matchable conclusion (a `Or` b) context inferred Match where
    match = elim @conclusion @(a `Or` b) @context @inferred

instance {-# OVERLAPPABLE #-} -- fallback
    Matchable conclusion premise context inferred mode where
    match = Nothing

-- Projectable --
instance
    Projectable conclusion '[] where
    project = Nothing

instance {-# OVERLAPPING #-}
    Projectable conclusion (conclusion ': context) where
    project = Just hHead

instance {-# OVERLAPPABLE #-}
    ( Projectable conclusion context
    ) => Projectable conclusion (premise ': context) where
    project = (. hTail) <$> project @conclusion @context

-- Intro --
instance {-# OVERLAPPING #-}
    Introducible True context inferred where
    intro = Just $ const ()

instance {-# OVERLAPPING #-}
    ( HCons a context
    , Deducible b (Insert a context) inferred
    ) => Introducible (a -> b) context inferred where
    intro = (\b ctxt a -> b $ hCons a ctxt)
        <$> deduce @b @(Insert a context) @inferred

instance {-# OVERLAPPING #-}
    ( Deducible a context inferred
    , Deducible b context inferred
    ) => Introducible (a `And` b) context inferred where
    intro = (\a b ctxt -> (a ctxt, b ctxt))
        <$> deduce @a @context @inferred
        <*> deduce @b @context @inferred

instance {-# OVERLAPPING #-}
    ( Deducible a context inferred
    , Deducible b context inferred
    ) => Introducible (a `Or` b) context inferred where
    intro = case deduce @a @context @inferred of
        Just a -> (\a ctxt -> Left $ a ctxt)
            <$> Just a
        Nothing -> (\b ctxt -> Right $ b ctxt)
            <$> deduce @b @context @inferred

instance {-# OVERLAPPABLE #-} -- fallback
    Introducible conclusion context inferred where
    intro = Nothing

-- Elim --
instance {-# OVERLAPPING #-}
    ( Traversable (a -> conclusion) context context inferred Find
    , Deducible a context inferred
    ) => Eliminable conclusion (a -> conclusion) context inferred where
    elim = (\f a ctxt -> f ctxt $ a ctxt)
        <$> traverse @(a -> conclusion) @context @context @inferred @Find
        <*> deduce @a @context @inferred

instance {-# OVERLAPPING #-}
    ( Traversable (conclusion `And` b) context context inferred Find
    ) => Eliminable conclusion (conclusion `And` b) context inferred where
    elim = (\ab ctxt -> fst $ ab ctxt)
        <$> traverse @(conclusion `And` b) @context @context @inferred @Find

instance {-# OVERLAPPING #-}
    ( Traversable (a `And` conclusion) context context inferred Find
    ) => Eliminable conclusion (a `And` conclusion) context inferred where
    elim = (\ab ctxt -> snd $ ab ctxt)
        <$> traverse @(a `And` conclusion) @context @context @inferred @Find

instance {-# OVERLAPPING #-}
    ( Traversable (a `Or` b) context context inferred Find
    , HCons a context
    , HCons b context
    , Deducible conclusion (Insert a context) inferred
    , Deducible conclusion (Insert b context) inferred
    ) => Eliminable conclusion (a `Or` b) context inferred where
    elim = (\ab ac bc ctxt -> case ab ctxt of
        Left a -> ac $ hCons a ctxt
        Right b -> bc $ hCons b ctxt)
            <$> traverse @(a `Or` b) @context @context @inferred @Find
            <*> deduce @conclusion @(Insert a context) @inferred
            <*> deduce @conclusion @(Insert b context) @inferred
            
instance {-# OVERLAPPABLE #-}
    Eliminable conclusion premise context inferred where
    elim = Nothing