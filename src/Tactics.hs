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


-- === Tactics === --
apply :: (a -> b) -> Tactic b a ()
apply f = Tactic $ \a -> f (a ())

left :: Tactic (a `Or` b) a ()
left = Tactic $ \a -> Left (a ())

right :: Tactic (a `Or` b) b ()
right = Tactic $ \b -> Right (b ())

intro :: Tactic (a -> b) b a
intro = Tactic id

exact :: a -> Tactic a () ()
exact a = Tactic $ const a

split :: Tactic a () () -> Tactic b () () -> Tactic (a `And` b) () ()
split (Tactic a) (Tactic b) = Tactic $ \id -> (a id, b id)

assert :: Tactic a () () -> Tactic m m a
assert (Tactic a) = ireturn $ a id

qed :: Tactic () () ()
qed = ireturn ()
