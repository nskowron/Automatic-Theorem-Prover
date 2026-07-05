{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Search where


import Proposition
import Inference

import Control.Monad ( join )
import Control.Applicative ( (<|>) )
import Data.HList ( HList(..), hHead, hTail )
import Data.Kind ( Type )


-- Proof Tree Search Node
-- Allows for iterating through context and
-- applying the right inference rules based on instance
type SearchNodes premises conclusion context = HList premises -> HList context -> conclusion
type SearchNode premise conclusion context = premise -> HList context -> conclusion

class Searchable a where
    search :: Maybe a

instance {-# OVERLAPPABLE #-}
    ( Searchable (SearchNode a b context)
    , Searchable (SearchNodes as b context)
    ) => Searchable (SearchNodes (a ': as) b context) where
    search = (. hHead) <$> search @(SearchNode a b context)
        <|> (. hTail) <$> search @(SearchNodes as b context)

instance {-# OVERLAPPING #-} Searchable (SearchNodes '[] True context) where
    search = pure . const . const $ ()

instance {-# OVERLAPPING #-} Searchable (SearchNodes '[] False context) where
    search = Nothing

instance {-# OVERLAPPING #-} Searchable (SearchNode a a context) where
    search = pure proj

instance {-# OVERLAPPABLE #-} Searchable (SearchNode a b context) where
    search = Nothing

instance {-# OVERLAPPABLE #-} Searchable (SearchNodes '[] (PS a) context) where
    search = Nothing

instance Searchable (SearchNodes (a ': context) b (a ': context))
    => Searchable (SearchNodes '[] (a `Impl` b) context) where
    search = const . implIntr . join
        <$> search @(SearchNodes (a ': context) b (a ': context))

instance 
    ( Searchable (SearchNodes context a context)
    , Searchable (SearchNodes context b context)
    ) => Searchable (SearchNodes '[] (a `And` b) context) where
    search = (const .) . (. join) . conjIntr . join
        <$> search @(SearchNodes context a context)
        <*> search @(SearchNodes context b context)

instance 
    ( Searchable (SearchNodes context a context)
    , Searchable (SearchNodes context b context)
    ) => Searchable (SearchNodes '[] (a `Or` b) context) where
    search = case search @(SearchNodes context a context) of
        Just a -> pure . const . disjIntr . Left . join $ a
        Nothing -> const . disjIntr . Right . join
            <$> search @(SearchNodes context b context)

instance Searchable (SearchNodes context a context)
    => Searchable (SearchNode (a `Impl` b) b context) where
    search = (. const) . flip implElim . join
        <$> search @(SearchNodes context a context)

instance Searchable (SearchNode (a `And` b) a context) where
    search = pure $ conjElimLeft . const

instance Searchable (SearchNode (a `And` b) b context) where
    search = pure $ conjElimRight . const

instance Searchable (SearchNode (a `Or` b) c context) where
    search = (\ac bc ab -> disjElim (const ab) (join ac) (join bc))
        <$> search @(SearchNodes (a ': context) c (a ': context))
        <*> search @(SearchNodes (b ': context) c (b ': context))