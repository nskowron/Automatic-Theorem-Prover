{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}

module Inference where

import Proposition
import HSet

import Control.Applicative ( (<|>) )
import Data.Kind ( Type )

import Prelude hiding ( Traversable, traverse )


-- === DECLARATIONS === --

-- match Algorithm --
class Inferable conclusion context where
    infer :: Maybe (HSet context -> conclusion)

class Traversable conclusion premises context where
    traverse :: Maybe (HSet context -> conclusion)

class Matchable conclusion premise context where
    match :: Maybe (HSet context -> conclusion)


-- Inference Rules --
class Projectable conclusion context where
    project :: Maybe (HSet context -> conclusion)

class Introducible conclusion context where
    intro :: Maybe (HSet context -> conclusion)

class Eliminable conclusion premise context where
    elim :: Maybe (HSet context -> conclusion)


-- === IMPLEMENTATION === --

-- Inferable
instance
    ( Introducible conclusion context
    , Traversable conclusion context context
    ) => Inferable conclusion context where
    infer = intro @conclusion @context
        <|> traverse @conclusion @context @context

-- Traversable --
instance
    Traversable conclusion '[] context where
    traverse = Nothing

instance {-# OVERLAPPING #-}
    ( Projectable conclusion context
    ) => Traversable conclusion (conclusion ': premises) context where
    traverse = project @conclusion @context

instance {-# OVERLAPPABLE #-}
    ( Matchable conclusion premise context
    , Traversable conclusion premises context
    ) => Traversable conclusion (premise ': premises) context where
    traverse = match @conclusion @premise @context
        <|> traverse @conclusion @premises @context

-- Matchable --
instance {-# OVERLAPPING #-} 
    ( Eliminable conclusion (a -> b) context
    , Matchable conclusion b context
    ) => Matchable conclusion (a -> b) context where
    match = elim @conclusion @(a -> b) @context
        <|> match @conclusion @b @context

instance {-# OVERLAPPING #-}
    ( Eliminable conclusion (a `And` b) context
    , Matchable conclusion a context
    , Matchable conclusion b context
    ) => Matchable conclusion (a `And` b) context where
    match = elim @conclusion @(a `And` b) @context
        <|> match @conclusion @a @context
        <|> match @conclusion @b @context

instance {-# OVERLAPPING #-} 
    ( Eliminable conclusion (a `Or` b) context
    ) => Matchable conclusion (a `Or` b) context where
    match = elim @conclusion @(a `Or` b) @context

-- fallback
instance {-# OVERLAPPABLE #-} 
    Matchable conclusion premise context where
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
    Introducible True context where
    intro = Just $ const ()

instance {-# OVERLAPPING #-}
    ( HCons a context
    , Inferable b (Insert a context)
    ) => Introducible (a -> b) context where
    intro = (\b ctxt a -> b $ hCons a ctxt)
        <$> infer @b @(Insert a context)

instance {-# OVERLAPPING #-}
    ( Inferable a context
    , Inferable b context
    ) => Introducible (a `And` b) context where
    intro = (\a b ctxt -> (a ctxt, b ctxt))
        <$> infer @a @context
        <*> infer @b @context

instance {-# OVERLAPPING #-}
    ( Inferable a context
    , Inferable b context
    ) => Introducible (a `Or` b) context where
    intro = case infer @a @context of
        Just a -> (\a ctxt -> Left $ a ctxt)
            <$> Just a
        Nothing -> (\b ctxt -> Right $ b ctxt)
            <$> infer @b @context

-- fallback
instance {-# OVERLAPPABLE #-}
    Introducible conclusion context where
    intro = Nothing

-- Elim --
instance {-# OVERLAPPING #-}
    ( Traversable (a -> conclusion) context context
    , Inferable a context
    ) => Eliminable conclusion (a -> conclusion) context where
    elim = (\f a ctxt -> f ctxt $ a ctxt)
        <$> traverse @(a -> conclusion) @context @context
        <*> infer @a @context

instance {-# OVERLAPPING #-}
    ( Traversable (conclusion `And` b) context context
    ) => Eliminable conclusion (conclusion `And` b) context where
    elim = (\ab ctxt -> fst $ ab ctxt)
        <$> traverse @(conclusion `And` b) @context @context
        
instance {-# OVERLAPPING #-}
    ( Traversable (a `And` conclusion) context context
    ) => Eliminable conclusion (a `And` conclusion) context where
    elim = (\ab ctxt -> snd $ ab ctxt)
        <$> traverse @(a `And` conclusion) @context @context

instance {-# OVERLAPPING #-}
    ( Traversable (a `Or` b) context context
    , HCons a context
    , HCons b context
    , Inferable conclusion (Insert a context)
    , Inferable conclusion (Insert b context)
    ) => Eliminable conclusion (a `Or` b) context where
    elim = (\ab ac bc ctxt -> case ab ctxt of
            Left a -> ac $ hCons a ctxt
            Right b -> bc $ hCons b ctxt)
        <$> traverse @(a `Or` b) @context @context
        <*> infer @conclusion @(Insert a context)
        <*> infer @conclusion @(Insert b context)

instance {-# OVERLAPPABLE #-}
    Eliminable conclusion premise context where
    elim = Nothing
