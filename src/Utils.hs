{-# LANGUAGE DataKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Utils where

import Data.Kind ( Type )


class Member e l where
    member :: Bool

instance
    Member e '[] where
    member = False

instance {-# OVERLAPPING #-}
    Member e (e ': l) where
    member = True

instance {-# OVERLAPPABLE #-}
    ( Member e ls
    ) => Member e (l ': ls) where
    member = member @e @ls
