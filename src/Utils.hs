module Utils where

import Proposition

import Data.Type.Nat ( Nat(..) )


-- === Utils === --
type family Member a l where
    Member a '[] = False
    Member a (a ': l) = True
    Member a (l ': ls) = Member a ls

type family If p a b where
    If True a _ = a
    If (True `And` True) a _ = a
    If (True `Or` _) a _ = a
    If (_ `Or` True) a _ = a
    If false _ b = b

type family FromMaybe d a where
    FromMaybe d Nothing = d
    FromMaybe _ (Just a) = a

type family Insert e l where
    Insert e '[] = '[e]
    Insert e (e ': l) = e ': l
    Insert e (l ': ls) = l ': Insert e ls

type family IsNat a where
    IsNat Z = True
    IsNat (S n) = True
    IsNat a = False

type family LookUp x ls where
    LookUp x ('(x, l) ': _) = l
    LookUp x ('(y, l) ': ls) = LookUp x ls


-- === Instantiable === --
class Instantiable a where
    type Demoted a
    instantiate :: Demoted a


-- === Maybe === --
instance
    ( Instantiable a
    ) => Instantiable (Nothing :: Maybe a) where
    type instance Demoted (Nothing :: Maybe a) = Maybe (Demoted a)
    instantiate = Nothing

instance
    ( Instantiable a
    ) => Instantiable (Just a) where
    type instance Demoted (Just a) = Maybe (Demoted a)
    instantiate = Just $ instantiate @a

type family a :<|>: b where
    Just a :<|>: _ = Just a
    Nothing :<|>: b = b

type family f :<$>: a where
    _ :<$>: Nothing = Nothing
    f :<$>: Just a = Just (f a)

type family f :<*>: a where
    Nothing :<*>: _ = Nothing
    _ :<*>: Nothing = Nothing
    Just f :<*>: Just a = Just (f a)


-- === Showtype === --
class ShowType a where
    showType :: String
