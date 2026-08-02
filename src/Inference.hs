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
class Inferable (conclusion :: Type) (context :: [Type]) (matched :: [(Type, Type, [Type])]) where
    infer :: Maybe (HSet context -> conclusion)

class Traversable (conclusion :: Type) (premises :: [Type]) (context :: [Type]) (matched :: [(Type, Type, [Type])]) where
    traverse :: Maybe (HSet context -> conclusion)

class Matchable (conclusion :: Type) (premise :: Type) (context :: [Type]) (matched :: [(Type, Type, [Type])]) where
    match :: 
        ( Member '(conclusion, premise, context) matched
        , Matchable conclusion premise context (Insert '(conclusion, premise, context) matched)
        ) => Maybe (HSet context -> conclusion)
    unmatched :: Maybe (HSet context -> conclusion)

    match
        | member @'(conclusion, premise, context) @matched = Nothing
        | otherwise = unmatched @conclusion @premise @context @(Insert '(conclusion, premise, context) matched)

    {-# MINIMAL unmatched #-}


-- Inference Rules --
class Projectable conclusion context where
    project :: Maybe (HSet context -> conclusion)

class Introducible conclusion context matched where
    intro :: Maybe (HSet context -> conclusion)

class Eliminable conclusion premise context matched where
    elim :: Maybe (HSet context -> conclusion)


-- === IMPLEMENTATION === --

-- Inferable
instance
    ( Introducible conclusion context matched
    , Traversable conclusion context context matched
    ) => Inferable conclusion context matched where
    infer = intro @conclusion @context @matched
        <|> traverse @conclusion @context @context @matched

-- Traversable --
instance
    Traversable conclusion '[] context matched where
    traverse = Nothing

instance {-# OVERLAPPING #-}
    ( Projectable conclusion context
    ) => Traversable conclusion (conclusion ': premises) context matched where
    traverse = project @conclusion @context

instance {-# OVERLAPPABLE #-}
    ( Member '(conclusion, premise, context) matched
    , Matchable conclusion premise context matched
    , Traversable conclusion premises context matched
    ) => Traversable conclusion (premise ': premises) context matched where
    traverse = match @conclusion @premise @context @matched
        <|> traverse @conclusion @premises @context @matched

-- Matchable --
instance {-# OVERLAPPING #-} 
    ( Member '(conclusion, b, context) matched
    , Eliminable conclusion (a -> b) context matched
    , Matchable conclusion b context matched
    ) => Matchable conclusion (a -> b) context matched where
    unmatched = elim @conclusion @(a -> b) @context @matched
        <|> match @conclusion @b @context @matched

instance {-# OVERLAPPING #-}
    ( Eliminable conclusion (a `And` b) context matched
    , Member '(conclusion, a, context) matched
    , Member '(conclusion, b, context) matched
    , Matchable conclusion a context matched
    , Matchable conclusion b context matched
    ) => Matchable conclusion (a `And` b) context matched where
    unmatched = elim @conclusion @(a `And` b) @context @matched
        <|> match @conclusion @a @context @matched
        <|> match @conclusion @b @context @matched

instance {-# OVERLAPPING #-} 
    ( Eliminable conclusion (a `Or` b) context matched
    ) => Matchable conclusion (a `Or` b) context matched where
    unmatched = elim @conclusion @(a `Or` b) @context @matched

-- fallback
instance {-# OVERLAPPABLE #-} 
    Matchable conclusion premise context matched where
    unmatched = Nothing


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
    Introducible True context matched where
    intro = Just $ const ()

instance {-# OVERLAPPING #-}
    ( HCons a context
    , Inferable b (Insert a context) matched
    ) => Introducible (a -> b) context matched where
    intro = (\b ctxt a -> b $ hCons a ctxt)
        <$> infer @b @(Insert a context) @matched

instance {-# OVERLAPPING #-}
    ( Inferable a context matched
    , Inferable b context matched
    ) => Introducible (a `And` b) context matched where
    intro = (\a b ctxt -> (a ctxt, b ctxt))
        <$> infer @a @context @matched
        <*> infer @b @context @matched

instance {-# OVERLAPPING #-}
    ( Inferable a context matched
    , Inferable b context matched
    ) => Introducible (a `Or` b) context matched where
    intro = case infer @a @context @matched of
        Just a -> (\a ctxt -> Left $ a ctxt)
            <$> Just a
        Nothing -> (\b ctxt -> Right $ b ctxt)
            <$> infer @b @context @matched

-- fallback
instance {-# OVERLAPPABLE #-}
    Introducible conclusion context matched where
    intro = Nothing

-- Elim --
instance {-# OVERLAPPING #-}
    ( Traversable (a -> conclusion) context context matched
    , Inferable a context matched
    ) => Eliminable conclusion (a -> conclusion) context matched where
    elim = (\f a ctxt -> f ctxt $ a ctxt)
        <$> traverse @(a -> conclusion) @context @context @matched
        <*> infer @a @context @matched

instance {-# OVERLAPPING #-}
    ( Traversable (conclusion `And` b) context context matched
    ) => Eliminable conclusion (conclusion `And` b) context matched where
    elim = (\ab ctxt -> fst $ ab ctxt)
        <$> traverse @(conclusion `And` b) @context @context @matched
        
instance {-# OVERLAPPING #-}
    ( Traversable (a `And` conclusion) context context matched
    ) => Eliminable conclusion (a `And` conclusion) context matched where
    elim = (\ab ctxt -> snd $ ab ctxt)
        <$> traverse @(a `And` conclusion) @context @context @matched

instance {-# OVERLAPPING #-}
    ( Traversable (a `Or` b) context context matched
    , HCons a context
    , HCons b context
    , Inferable conclusion (Insert a context) matched
    , Inferable conclusion (Insert b context) matched
    ) => Eliminable conclusion (a `Or` b) context matched where
    elim = (\ab ac bc ctxt -> case ab ctxt of
            Left a -> ac $ hCons a ctxt
            Right b -> bc $ hCons b ctxt)
        <$> traverse @(a `Or` b) @context @context @matched
        <*> infer @conclusion @(Insert a context) @matched
        <*> infer @conclusion @(Insert b context) @matched

instance {-# OVERLAPPABLE #-}
    Eliminable conclusion premise context matched where
    elim = Nothing
