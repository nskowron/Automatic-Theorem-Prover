{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module HList where

import Data.Kind
import Data.Void
import Data.Type.Equality (type (==))

data HList (l :: [Type]) where
    HNil  :: HList '[]
    HCons :: e -> HList l -> HList (e ': l)


type family If c a b where
    If 'True a b = a
    If 'False a b = b


type family Find s l

type instance Find s (HList '[]) = Void
type instance Find s (HList (t ': ts)) =
    If (s == t) 
        ()
        (Find s (HList ts))


class Proposition a where
    type ContextType a
    prove :: Maybe (ContextType a -> a)


newtype Match s ts where
    Match :: HList (s ': ts) -> Match s ts

newtype Matching s ts = Matching s

type family FindMatch s ts where
    FindMatch s (HList '[]) = Void
    FindMatch s (HList (t ': ts)) =
        If (s == t)
            (Match s ts)
            (Matching s (HList (t ': ts)))

instance Proposition (Match s ts) where
    type ContextType (Match s ts) = HList (s ': ts)
    prove = Just Match
