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
type SearchNodes premises conclusion context visited = HList premises -> HList context -> conclusion
type SearchNode premise conclusion context visited = premise -> HList context -> conclusion

class Searchable a where
    search :: Maybe a

instance {-# OVERLAPPABLE #-}
    ( Searchable (SearchNode a b context No)
    , Searchable (SearchNodes as b context No)
    ) => Searchable (SearchNodes (a ': as) b context No) where
    search = (. hHead) <$> search @(SearchNode a b context No)
        <|> (. hTail) <$> search @(SearchNodes as b context No)

instance {-# OVERLAPPING #-} Searchable (SearchNodes '[] True context No) where
    search = pure . const . const $ ()

instance {-# OVERLAPPING #-} Searchable (SearchNodes '[] False context No) where
    search = Nothing

instance {-# OVERLAPPING #-} Searchable (SearchNode a a context No) where
    search = pure proj

instance {-# OVERLAPPABLE #-} Searchable (SearchNodes '[] (PS a) context No) where
    search = Nothing

instance Searchable (SearchNodes (a ': context) b (a ': context) No)
    => Searchable (SearchNodes '[] (a `Impl` b) context No) where
    search = const . implIntr . join
        <$> search @(SearchNodes (a ': context) b (a ': context) No)

instance 
    ( Searchable (SearchNodes context a context No)
    , Searchable (SearchNodes context b context No)
    ) => Searchable (SearchNodes '[] (a `And` b) context No) where
    search = (const .) . (. join) . conjIntr . join
        <$> search @(SearchNodes context a context No)
        <*> search @(SearchNodes context b context No)

instance 
    ( Searchable (SearchNodes context a context No)
    , Searchable (SearchNodes context b context No)
    ) => Searchable (SearchNodes '[] (a `Or` b) context No) where
    search = case search @(SearchNodes context a context No) of
        Just a -> pure . const . disjIntr . Left . join $ a
        Nothing -> const . disjIntr . Right . join
            <$> search @(SearchNodes context b context No)

instance Searchable (SearchNodes context a context No)
    => Searchable (SearchNode (a `Impl` b) b context No) where
    search = (. const) . flip implElim . join
        <$> search @(SearchNodes context a context No)

instance Searchable (SearchNode (a `And` b) a context No) where
    search = pure $ conjElimLeft . const

instance Searchable (SearchNode (a `And` b) b context No) where
    search = pure $ conjElimRight . const

instance Searchable (SearchNode a b context Yes) where
    search = Nothing

instance
    ( Searchable (SearchNodes (a ': context) c (a ': context) Yes)
    , Searchable (SearchNodes (b ': context) c (b ': context) Yes)
    ) => Searchable (SearchNode (a `Or` b) c context No) where
    search = (\ac bc ab -> disjElim (const ab) (join ac) (join bc))
        <$> search @(SearchNodes (a ': context) c (a ': context) Yes)
        <*> search @(SearchNodes (b ': context) c (b ': context) Yes)
