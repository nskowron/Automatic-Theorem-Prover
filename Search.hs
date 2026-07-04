{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Search where


import Proposition
import Inference

import Data.HList ( HList(..) )

-- Searchable - describes proof tree nodes
class Searchable a where
    search :: Maybe a


-- instances of Searchable - determine the deduction rules
-- used to prove each type of proposition
-- for now just the basic deduction rules
-- TODO: add a method with all the deduction rules
-- and heuristics applicable for any proposition

-- True - always provable
instance Searchable (HList c -> True) where
    search = Just $ const ()

-- False - never provable
instance Searchable (HList c -> False) where
    search = Nothing

-- Implication a -> b - provable if b is provable while assuming a
instance Searchable (HList (a ': c) -> b) => Searchable (HList c -> Impl a b) where
    search = fmap (\proof -> \ctxt -> \x -> proof (HCons x ctxt)) (search @(HList (a ': c) -> b))

-- And (a, b) - provable if both a and b provable
instance (Searchable (HList c -> a), Searchable (HList c -> b)) => Searchable (HList c -> And a b) where
    search = liftA2 (\p1 p2 -> \ctxt -> (p1 ctxt, p2 ctxt)) (search @(HList c -> a)) (search @(HList c -> b))

instance (Searchable (HList c -> a), Searchable (HList c -> b)) => Searchable (HList c -> Or a b) where
    search = case (search @(HList c -> a)) of
        Nothing -> fmap (\proof -> \ctxt -> Right (proof ctxt)) (search @(HList c -> b))
        proof -> fmap (\proof -> \ctxt -> Left (proof ctxt)) proof

-- PS a - provable if found in context
instance (Iterable (IterNext (HList c -> PS a)), (SearchedType (IterNext (HList c -> PS a)) ~ (HList c -> PS a))) 
    => Searchable (HList c -> PS a) where
    search = iter @(IterNext (HList c -> PS a))


-- Iterating over context type
-- its not clean yet, i dont like it, will try to reformat

-- phantom types for Iterable instance deduction
data Match a
data NoMatch a

-- decides on the phantom type
type family IterNext ts where
    IterNext (HList (s ': ts) -> s) = Match (HList (s ': ts) -> s)
    IterNext  ts = NoMatch ts


-- Iterable - has a type to search for and maybe finds it
class Iterable a where
    type SearchedType a
    iter :: Maybe (SearchedType a)

-- instances of Iterable - determine how to search the context

-- empty context - not found
instance Iterable (NoMatch (HList '[] -> s)) where
    type instance SearchedType (NoMatch (HList '[] -> s)) = HList '[] -> s
    iter = Nothing

-- found searched type - return it
instance Iterable (Match (HList (s ': ts) -> s)) where
    type instance SearchedType (Match (HList (s ': ts) -> s)) = HList (s ': ts) -> s
    iter = Just $ \(HCons c _) -> c

-- types dont match - iterate further
instance (Iterable (IterNext (HList ts -> s)), (SearchedType (IterNext (HList ts -> s)) ~ (HList ts -> s))) 
    => Iterable (NoMatch (HList (t ': ts) -> s)) where
    type instance SearchedType (NoMatch (HList (t ': ts) -> s)) = HList (t ': ts) -> s
    iter = fmap (\found -> \(HCons c cs) -> found cs) (iter @(IterNext (HList ts -> s)))