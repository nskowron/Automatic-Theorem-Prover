{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Search where

import Proposition

import Control.Applicative ( (<|>) )
import Data.HList ( HList(..) )
import Data.Kind ( Type )


class Member a l where
    member :: Bool

instance Member a '[] where
    member = False

instance {-# OVERLAPPING #-} Member a (a ': ls) where
    member = True 

instance {-# OVERLAPPABLE #-} (Member a ls) => Member a (l ': ls) where
    member = member @a @ls

class Searchable (conclusion :: Type) (premises :: [Type]) (context :: [Type]) (tabu_concl :: [Type]) (tabu_prem :: [Type]) where
    search :: HList premises -> Maybe (HList context -> conclusion)

class Inferable (conclusion :: Type) (premise :: Type) (context :: [Type]) (tabu_concl :: [Type]) (tabu_prem :: [Type]) where
    infer :: premise -> Maybe (HList context -> conclusion)

-- placeholders for compilation
instance {-# OVERLAPPING #-} Inferable () premise context tabu_concl tabu_prem where -- rem overl later
    infer _ = Just $ const ()

instance {-# OVERLAPPABLE #-} Inferable conclusion premise context tabu_concl tabu_prem where
    infer _ = Nothing

instance
    ( Member conclusion tabu_concl
    , Member premise tabu_prem
    , Inferable conclusion premise context tabu_concl tabu_prem
    , Searchable conclusion premises context tabu_concl tabu_prem
    ) => Searchable conclusion (premise ': premises) context tabu_concl tabu_prem where
    search (HCons p ps) =
        ( if member @conclusion @tabu_concl || member @premise @tabu_prem
        then Nothing
        else infer @conclusion @premise @context @tabu_concl @tabu_prem p
        ) <|> search @conclusion @premises @context @tabu_concl @tabu_prem ps

instance 
    ( Member conclusion tabu_concl
    , Inferable conclusion () context tabu_concl tabu_prem
    ) => Searchable conclusion '[] context tabu_concl tabu_prem where
    search HNil =
        if member @conclusion @tabu_concl
        then Nothing
        else infer @conclusion @() @context @tabu_concl @tabu_prem () --intro rule for ()?

-- TODO:

-- class Inferable node conclusion premise context
--     | node -> conclusion premise context where
--     infer :: premise -> Maybe (context -> conclusion)