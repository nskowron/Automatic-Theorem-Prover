{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

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
instance {-# OVERLAPPING #-} 
    ( Member (a -> conclusion) tabu_prem
    , Inferable conclusion '[a, a -> conclusion] context tabu_concl tabu_prem
    , Searchable conclusion premises context tabu_concl tabu_prem
    ) => Searchable conclusion ((a -> conclusion) ': premises) context tabu_concl tabu_prem where
    search = 
        if member @(a -> conclusion) @tabu_prem
        then Nothing
        else infer @conclusion @'[a, a -> conclusion] @context @tabu_concl @tabu_prem
            <|> search @conclusion @premises @context @tabu_concl @tabu_prem

-- TODO: remember to add to tabu premises
instance {-# OVERLAPPABLE #-} 
    ( Member (a -> b) tabu_prem
    , Searchable conclusion (b ': premises) context tabu_concl tabu_prem
    ) => Searchable conclusion ((a -> b) ': premises) context tabu_concl tabu_prem where
    search = 
        if member @(a -> b) @tabu_prem
        then Nothing
        else search @conclusion @(b ': premises) @context @tabu_concl @tabu_prem

-- TODO: maybe a rule for False being in the premises? and add absurd?

-- fallback for now
instance {-# OVERLAPPABLE #-} 
    ( Searchable conclusion premises context tabu_concl tabu_prem
    ) => Searchable conclusion (premise ': premises) context tabu_concl tabu_prem where
    search = search @conclusion @premises @context @tabu_concl @tabu_prem

-- inference rules

-- intro
instance Inferable True '[] context tabu_concl tabu_prem where
    infer = Just $ const ()

instance Inferable False '[] context tabu_concl tabu_prem where
    infer = Nothing

-- TODO: the ():context is very unefective, comparing contexts
instance 
    ( Searchable b (() ': a ': context) (a ': context) tabu_concl tabu_prem
    ) => Inferable (a `Impl` b) '[] context tabu_concl tabu_prem where
    infer = (\b -> \ctxt -> \a -> b (HCons a ctxt))
        <$> search @b @(() ': a ': context) @(a ': context) @tabu_concl @tabu_prem

instance Inferable (PS a) '[] context tabu_concl tabu_prem where
    infer = Nothing
