{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module HSet
    ( HSet
    , HCons
    , HList(HNil)
    , hCons
    , hHead
    , hTail
    , Insert
    ) where

import Data.HList ( HList(..), hHead, hTail )
import Data.Kind ( Type )


type HSet = HList

type family Insert e l where
    Insert e '[] = '[e]
    Insert e (e ': l) = e ': l
    Insert e (l ': ls) = l ': (Insert e ls)

class HCons e l where
    hCons :: e -> HSet l -> HSet (Insert e l)

instance
    HCons e '[] where
    hCons x HNil = HCons x HNil

instance {-# OVERLAPPING #-} 
    HCons e (e ': l) where
    hCons x l = l

instance {-# OVERLAPPABLE #-} 
    ( HCons e ls
    , Insert e (l ': ls) ~ l ': (Insert e ls)
    ) => HCons e (l ': ls) where
    hCons x (HCons l ls) = HCons l (hCons x ls)
