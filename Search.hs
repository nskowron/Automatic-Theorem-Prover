{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}

module Search where

import Proposition

import Control.Applicative ( (<|>) )
import Data.HList ( HList(..), hHead, hTail )
import Data.Kind ( Type )


-- class Member a l where
--     member :: Bool

-- instance Member a '[] where
--     member = False

-- instance {-# OVERLAPPING #-} Member a (a ': ls) where
--     member = True 

-- instance {-# OVERLAPPABLE #-} (Member a ls) => Member a (l ': ls) where
--     member = member @a @ls

class Find a l where
    find :: Maybe (HList l -> a)

instance Find a '[] where
    find = Nothing

instance {-# OVERLAPPING #-} Find a (a ': ls) where
    find = Just hHead

instance {-# OVERLAPPABLE #-} (Find a ls) => Find a (l ': ls) where
    find = (. hTail) <$> find @a @ls

-- searches possible premises
class Searchable (conclusion :: Type) (premises :: [Type]) (context :: [Type]) where
    search :: Maybe (HList context -> conclusion)

-- infers from concrete premises
class Inferable (conclusion :: Type) (premises :: [Type]) (context :: [Type]) where
    infer :: Maybe (HList context -> conclusion)

instance Searchable conclusion '[] context where
    search = Nothing

instance {-# OVERLAPPING #-} 
    ( Find conclusion context
    , Inferable conclusion '[] context
    , Searchable conclusion context context
    ) => Searchable conclusion (() ': context) context where
    search = find @conclusion @context
        <|> infer @conclusion @'[] @context
        <|> search @conclusion @context @context

-- TODO: consider moving the ifs into another method and using MINIMAL
-- TODO: remember to add to tabu premises
-- TODO: think if b doesnt need to be added to context
-- TODO: maybe a rule for False being in the premises? and add absurd?
-- TODO: remove the list for infer premises
-- TODO: fix tabu on type level
instance {-# OVERLAPPING #-} 
    ( Inferable conclusion '[a -> b] context
    , Searchable conclusion '[b] context
    , Searchable conclusion premises context
    ) => Searchable conclusion ((a -> b) ': premises) context where
    search = search @conclusion @'[b] @context
        <|> infer @conclusion @'[a -> b] @context
        <|> search @conclusion @premises @context

instance {-# OVERLAPPING #-}
    ( Inferable conclusion '[a `And` b] context
    , Searchable conclusion '[a] context
    , Searchable conclusion '[b] context
    , Searchable conclusion premises context
    ) => Searchable conclusion ((a `And` b) ': premises) context where
    search = infer @conclusion @'[a `And` b] @context
        <|> search @conclusion @'[a] @context
        <|> search @conclusion @'[b] @context
        <|> search @conclusion @premises @context

instance {-# OVERLAPPING #-} 
    ( Inferable conclusion '[a `Or` b] context
    , Searchable conclusion premises context
    ) => Searchable conclusion ((a `Or` b) ': premises) context where
    search = infer @conclusion @'[a `Or` b] @context
        <|> search @conclusion @premises @context

-- fallback - skip
instance {-# OVERLAPPABLE #-} 
    ( Searchable conclusion premises context
    ) => Searchable conclusion (premise ': premises) context where
    search = search @conclusion @premises @context

-- inference rules

-- intro
instance {-# OVERLAPPING #-}
    Inferable True '[] context where
    infer = Just $ const ()

-- TODO: the ():context is very unefective, comparing contexts
instance {-# OVERLAPPING #-}
    ( Searchable b (() ': a ': context) (a ': context)
    ) => Inferable (a -> b) '[] context where
    infer = (\b ctxt a -> b $ HCons a ctxt)
        <$> search @b @(() ': a ': context) @(a ': context)

instance {-# OVERLAPPING #-}
    ( Searchable a (() ': context) context
    , Searchable b (() ': context) context
    ) => Inferable (a `And` b) '[] context where
    infer = (\a b ctxt -> (a ctxt, b ctxt))
        <$> search @a @(() ': context) @context
        <*> search @b @(() ': context) @context

instance {-# OVERLAPPING #-}
    ( Searchable a (() ': context) context
    , Searchable b (() ': context) context
    ) => Inferable (a `Or` b) '[] context where
    infer = case search @a @(() ': context) @context of
        Just a -> (\a ctxt -> Left $ a ctxt) <$> Just a
        Nothing -> (\b ctxt -> Right $ b ctxt)
            <$> search @b @(() ': context) @context

-- fallback
instance {-# OVERLAPPABLE #-}
    Inferable conclusion '[] context where
    infer = Nothing

-- elim
instance {-# OVERLAPPING #-}
    ( Find (a -> conclusion) context
    , Searchable a (() ': context) context
    ) => Inferable conclusion '[a -> conclusion] context where
    infer = (\f a ctxt -> f ctxt $ a ctxt)
        <$> find @(a -> conclusion) @context
        <*> search @a @(() ': context) @context

instance {-# OVERLAPPING #-}
    ( Find (conclusion `And` b) context
    ) => Inferable conclusion '[conclusion `And` b] context where
    infer = (\ab ctxt -> fst $ ab ctxt)
        <$> find @(conclusion `And` b) @context
        
instance {-# OVERLAPPING #-}
    ( Find (a `And` conclusion) context
    ) => Inferable conclusion '[a `And` conclusion] context where
    infer = (\ab ctxt -> snd $ ab ctxt)
        <$> find @(a `And` conclusion) @context

instance {-# OVERLAPPING #-}
    ( Find (a `Or` b) context
    , Searchable conclusion '[a] (a ': context)
    , Searchable conclusion '[b] (b ': context)
    ) => Inferable conclusion '[a `Or` b] context where
    infer = (\ab ac bc ctxt -> case ab ctxt of
            Left a -> ac $ HCons a ctxt
            Right b -> bc $ HCons b ctxt)
        <$> find @(a `Or` b) @context
        <*> search @conclusion @'[a] @(a ': context)
        <*> search @conclusion @'[b] @(b ': context)

instance {-# OVERLAPPABLE #-}
    Inferable conclusion premises context where
    infer = Nothing
