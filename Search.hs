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


class Member a l where
    member :: Bool

instance Member a '[] where
    member = False

instance {-# OVERLAPPING #-} Member a (a ': ls) where
    member = True 

instance {-# OVERLAPPABLE #-} (Member a ls) => Member a (l ': ls) where
    member = member @a @ls

class Find a l where
    find :: Maybe (HList l -> a)

instance Find a '[] where
    find = Nothing

instance {-# OVERLAPPING #-} Find a (a ': ls) where
    find = Just hHead

instance {-# OVERLAPPABLE #-} (Find a ls) => Find a (l ': ls) where
    find = (. hTail) <$> find @a @ls

-- searches possible premises
class Searchable (conclusion :: Type) (premises :: [Type]) (context :: [Type]) (tabu_concl :: [Type]) (tabu_prem :: [Type]) where
    search :: Maybe (HList context -> conclusion)

-- infers from concrete premises
class Inferable (conclusion :: Type) (premises :: [Type]) (context :: [Type]) (tabu_concl :: [Type]) (tabu_prem :: [Type]) where
    infer :: Maybe (HList context -> conclusion)

instance Searchable conclusion '[] context tabu_concl tabu_prem where
    search = Nothing

instance {-# OVERLAPPING #-} 
    ( Find conclusion context
    , Member conclusion tabu_concl
    , Inferable conclusion '[] context tabu_concl tabu_prem
    , Searchable conclusion context context tabu_concl tabu_prem
    ) => Searchable conclusion (() ': context) context tabu_concl tabu_prem where
    search = find @conclusion @context
        <|> if member @conclusion @tabu_concl
            then Nothing
            else infer @conclusion @'[] @context @tabu_concl @tabu_prem
                <|> search @conclusion @context @context @tabu_concl @tabu_prem

-- TODO: consider moving the ifs into another method and using MINIMAL
-- TODO: remember to add to tabu premises
-- TODO: think if b doesnt need to be added to context
-- TODO: maybe a rule for False being in the premises? and add absurd?
-- TODO: remove the list for infer premises
-- TODO: fix tabu on type level
instance {-# OVERLAPPING #-} 
    ( Member (a -> b) tabu_prem
    , Inferable conclusion '[a -> b] context tabu_concl tabu_prem
    , Searchable conclusion '[b] context tabu_concl tabu_prem
    , Searchable conclusion premises context tabu_concl tabu_prem
    ) => Searchable conclusion ((a -> b) ': premises) context tabu_concl tabu_prem where
    search
        | member @(a -> b) @tabu_prem = Nothing
        | otherwise = search @conclusion @'[b] @context @tabu_concl @tabu_prem
            <|> infer @conclusion @'[a -> b] @context @tabu_concl @tabu_prem
            <|> search @conclusion @premises @context @tabu_concl @tabu_prem

instance {-# OVERLAPPING #-}
    ( Member (a `And` b) tabu_prem
    , Inferable conclusion '[a `And` b] context tabu_concl tabu_prem
    , Searchable conclusion '[a] context tabu_concl tabu_prem
    , Searchable conclusion '[b] context tabu_concl tabu_prem
    , Searchable conclusion premises context tabu_concl tabu_prem
    ) => Searchable conclusion ((a `And` b) ': premises) context tabu_concl tabu_prem where
    search
        | member @(a `And` b) @tabu_prem = Nothing
        | otherwise = infer @conclusion @'[a `And` b] @context @tabu_concl @tabu_prem
            <|> search @conclusion @'[a] @context @tabu_concl @tabu_prem
            <|> search @conclusion @'[b] @context @tabu_concl @tabu_prem
            <|> search @conclusion @premises @context @tabu_concl @tabu_prem

-- instance {-# OVERLAPPING #-} 
--     ( Member (a `Or` b) tabu_prem
--     , Inferable conclusion '[a `Or` b] context tabu_concl tabu_prem
--     , Searchable conclusion premises context tabu_concl tabu_prem
--     ) => Searchable conclusion ((a `Or` b) ': premises) context tabu_concl tabu_prem where
--     search
--         | member @(a `Or` b) @tabu_prem = Nothing
--         | otherwise = infer @conclusion @'[a `Or` b] @context @tabu_concl @tabu_prem
--             <|> search @conclusion @premises @context @tabu_concl @tabu_prem

-- fallback - skip
instance {-# OVERLAPPABLE #-} 
    ( Searchable conclusion premises context tabu_concl tabu_prem
    ) => Searchable conclusion (premise ': premises) context tabu_concl tabu_prem where
    search = search @conclusion @premises @context @tabu_concl @tabu_prem

-- inference rules

-- intro
instance {-# OVERLAPPING #-}
    Inferable True '[] context tabu_concl tabu_prem where
    infer = Just $ const ()

-- TODO: the ():context is very unefective, comparing contexts
instance {-# OVERLAPPING #-}
    ( Searchable b (() ': a ': context) (a ': context) tabu_concl tabu_prem
    ) => Inferable (a -> b) '[] context tabu_concl tabu_prem where
    infer = (\b ctxt a -> b $ HCons a ctxt)
        <$> search @b @(() ': a ': context) @(a ': context) @tabu_concl @tabu_prem

instance {-# OVERLAPPING #-}
    ( Searchable a (() ': context) context tabu_concl tabu_prem
    , Searchable b (() ': context) context tabu_concl tabu_prem
    ) => Inferable (a `And` b) '[] context tabu_concl tabu_prem where
    infer = (\a b ctxt -> (a ctxt, b ctxt))
        <$> search @a @(() ': context) @context @tabu_concl @tabu_prem
        <*> search @b @(() ': context) @context @tabu_concl @tabu_prem

instance {-# OVERLAPPING #-}
    ( Searchable a (() ': context) context tabu_concl tabu_prem
    , Searchable b (() ': context) context tabu_concl tabu_prem
    ) => Inferable (a `Or` b) '[] context tabu_concl tabu_prem where
    infer = case search @a @(() ': context) @context @tabu_concl @tabu_prem of
        Just a -> (\a ctxt -> Left $ a ctxt) <$> Just a
        Nothing -> (\b ctxt -> Right $ b ctxt)
            <$> search @b @(() ': context) @context @tabu_concl @tabu_prem

-- fallback
instance {-# OVERLAPPABLE #-}
    Inferable conclusion '[] context tabu_concl tabu_prem where
    infer = Nothing

-- elim
instance {-# OVERLAPPING #-}
    ( Searchable (a -> conclusion) (() ': context) context tabu_concl tabu_prem
    , Searchable a (() ': context) context tabu_concl tabu_prem
    ) => Inferable conclusion '[a -> conclusion] context tabu_concl tabu_prem where
    infer = (\f a ctxt -> f ctxt $ a ctxt)
        <$> search @(a -> conclusion) @(() ': context) @context @tabu_concl @tabu_prem
        <*> search @a @(() ': context) @context @tabu_concl @tabu_prem

instance {-# OVERLAPPING #-}
    ( Searchable (conclusion `And` b) (() ': context) context tabu_concl tabu_prem
    ) => Inferable conclusion '[conclusion `And` b] context tabu_concl tabu_prem where
    infer = (\ab ctxt -> fst $ ab ctxt)
        <$> search @(conclusion `And` b) @(() ': context) @context @tabu_concl @tabu_prem

instance {-# OVERLAPPING #-}
    ( Searchable (a `And` conclusion) (() ': context) context tabu_concl tabu_prem
    ) => Inferable conclusion '[a `And` conclusion] context tabu_concl tabu_prem where
    infer = (\ab ctxt -> snd $ ab ctxt)
        <$> search @(a `And` conclusion) @(() ': context) @context @tabu_concl @tabu_prem

-- instance {-# OVERLAPPING #-}
--     ( Searchable (a `Or` b) (() ': context) context tabu_concl tabu_prem
--     , Searchable conclusion (() ': a ': context) (a ': context) tabu_concl tabu_prem
--     , Searchable conclusion (() ': b ': context) (b ': context) tabu_concl tabu_prem
--     ) => Inferable conclusion '[a `Or` b] context tabu_concl tabu_prem where
--     infer = (\ab ac bc ctxt -> case ab ctxt of
--             Left a -> ac $ HCons a ctxt
--             Right b -> bc $ HCons b ctxt)
--         <$> search @(a `Or` b) @(() ': context) @context @tabu_concl @tabu_prem
--         <*> search @conclusion @(() ': a ': context) @(a ': context) @tabu_concl @tabu_prem
--         <*> search @conclusion @(() ': b ': context) @(b ': context) @tabu_concl @tabu_prem

instance {-# OVERLAPPABLE #-}
    Inferable conclusion premises context tabu_concl tabu_prem where
    infer = Nothing
