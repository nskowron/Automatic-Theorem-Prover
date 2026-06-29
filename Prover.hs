{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Prover where

import Data.Kind ( Type )
import Data.Void ( Void )

-- heterogenous list (used for passing context)
-- will replace with haskell library one
data HList (l :: [Type]) where
    HNil  :: HList '[]
    HCons :: e -> HList l -> HList (e ': l)


-- basic provable types
type True = ()
type False = Void
type Impl a b = a -> b
type And a b = (a, b)
newtype PS a = PS a -- Propositional Symbol


-- Searchable - describes proof tree nodes
class Searchable a where
    search :: Maybe a

-- Provable - describes provable propositions
class Provable a where
    prove :: Maybe a

-- each proof search tree node is (maybe) a function that
-- takes in the context and returns proof of a proposition
instance (Searchable (HList '[] -> a)) => Provable a where
    prove = fmap ($ HNil) (search @(HList '[] -> a))


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


-- helper
printProof :: Maybe a -> String
printProof Nothing = "Nothing"
printProof (Just _) = "Proof Successful"
