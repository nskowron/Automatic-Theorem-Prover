{-# LANGUAGE DataKinds #-}

module Inference where


import Proposition

import Data.HList ( HList(..) )


proj :: HList (a ': context) -> a
proj (HCons a _) = a

implIntr 
    :: (HList (a ': context) -> b) 
    -> HList context -> (a `Impl` b)
implIntr b context = \a -> b $ HCons a context 

implElim 
    :: (HList context -> a `Impl` b) -> (HList context -> a) 
    -> HList context -> b
implElim f a context = f context $ a context

conjIntr 
    :: (HList context -> a) -> (HList context -> b) 
    -> HList context -> (a `And` b)
conjIntr a b context = (a context, b context)

conjElimLeft 
    :: (HList context -> a `And` b)
    -> HList context -> a
conjElimLeft ab context = fst $ ab context

conjElimRight 
    :: (HList context -> a `And` b)
    -> HList context -> b
conjElimRight ab context = snd $ ab context

disjIntr 
    :: Either (HList context -> a) (HList context -> b)
    -> HList context -> a `Or` b
disjIntr (Left a) context = Left $ a context
disjIntr (Right b) context = Right $ b context

disjElim 
    :: (HList context -> a `Or` b) -> (HList (a ': context) -> c) -> (HList (b ': context) -> c)
    -> HList context -> c
disjElim ab ac bc context = case ab context of
    (Left a) -> ac $ HCons a context
    (Right b) -> bc $ HCons b context
