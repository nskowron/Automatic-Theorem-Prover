module Tactics where

import Proposition

import Control.Monad.Indexed


-- === Tactic === --
data Tactic from to a = Tactic ((a -> to) -> from)

instance IxFunctor Tactic where
    imap f (Tactic a) = Tactic $ \g -> a (g . f)

instance IxPointed Tactic where
    ireturn a = Tactic $ \f -> f a

instance IxApplicative Tactic where
    iap (Tactic f) (Tactic a) = Tactic $ \g -> f (\b -> a (g . b))

instance IxMonad Tactic where
    ibind f (Tactic a) = Tactic $ \g -> a (\b -> let Tactic h = f b in h g)
