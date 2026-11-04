module Search where

import SearchUtils
import Proposition
import ACFp ( F, (:+:), (:-:), (:*:), (:/:), (:^:) )
import FOL
import Utils
import Node

import Data.Kind ( Type )
import Data.Type.Nat


-- -- === Flag === --
-- data Flag = Search -- default, try to apply all inference rules
--     | Find -- try to find node in context, eg. no intro rules
--     | Stop -- used for loop detection


-- -- === MakeNode === --
-- type family MakeNode (flag :: Flag) (context :: [(Type, Nat)]) (conclusion :: Type) (n :: Nat) (parents :: [([(Type, Nat)], Type)]) :: Maybe Node where

--     MakeNode flag context conclusion n parents =
--         TryInfer
--             flag
--             -- (If (Member '(context, conclusion) parents)
--             --     Stop
--             --     flag)
--             context
--             conclusion
--             n
--             parents
--             -- (Insert '(context, conclusion) parents)
             


-- -- === Try Infer === --
-- type family TryInfer (flag :: Flag) (context :: [(Type, Nat)]) (conclusion :: Type) (n :: Nat) (parents :: [([(Type, Nat)], Type)]) :: Maybe Node where

--     TryInfer Search context (a -> b) n parents =
--         TryIntro context (a -> b) n parents

--     TryInfer Search context (Forall x a p) n parents =
--         TryIntro context (Forall x a p) n parents

--     TryInfer Search context (a `And` b) n parents =
--         TryIntro context (a `And` b) n parents

--     TryInfer Search context (Exists x a p) n parents =
--         TryProject context (Exists x a p)
--         :<|>: TryIntro context (Exists x a p) n parents
--         :<|>: TryElim Search context (Exists x a p) (Premises context) n parents

--     TryInfer Search context conclusion n parents =
--         TryProject context conclusion
--         :<|>: TryIntro context conclusion n parents
--         :<|>: TryElim Search context conclusion (Premises context) n parents

--     TryInfer Find context conclusion n parents =
--         TryProject context conclusion
--         :<|>: TryElim Find context conclusion (Premises context) n parents

--     TryInfer Stop _ _ _ _ = Nothing


-- -- === TryProject === --
-- type family TryProject (context :: [(Type, Nat)]) (conclusion :: Type) where

--     TryProject '[] conclusion = Nothing
--     TryProject ('(conclusion, n) ': context) conclusion = Just (Project n)
--     TryProject ('(premise, _) ': context) conclusion = TryProject context conclusion


-- -- === TryIntro === --
-- type family TryIntro (context :: [(Type, Nat)]) (conclusion :: Type) (n :: Nat) (parents :: [([(Type, Nat)], Type)]) :: Maybe Node where

--     TryIntro _ True _ _ =
--         Just IntroTrue

--     TryIntro context (a -> b) n parents =
--         IntroImpl
--             :<$>: MakeNode Search (Assume a context) b n parents  

--     TryIntro context (a `And` b) n parents =
--         IntroAnd
--             :<$>: MakeNode Search context a n parents
--             :<*>: MakeNode Search context b n parents

--     TryIntro context (a `Or` b) n parents =
--         (IntroOrLeft
--             :<$>: MakeNode Search context a n parents)
--         :<|>: (IntroOrRight
--             :<$>: MakeNode Search context b n parents)

--     TryIntro context (a :=: a) n parents =
--         Just Reflexivity

--     TryIntro context (Forall x a p) n parents =
--         IntroForall
--             :<$>: (IntroPredicate :<$>: MakeNode Search context (Substitute p x (X (S n))) (S n) parents)

--     TryIntro context (Exists x a p) n parents =
--         TryIntroExists context (Exists x a p) n n parents

--     TryIntro _ _ _ _ = Nothing

    
-- -- === TryIntroExists === --
-- type family TryIntroExists (context :: [(Type, Nat)]) (conclusion :: Type) (witness :: Nat) (n :: Nat) (parents :: [([(Type, Nat)], Type)]) :: Maybe Node where

--     TryIntroExists _ _ Z _ _ = Nothing

--     TryIntroExists context (Exists x a p) (S t) n parents =
--         IntroExists (X (S t))
--             :<$>: (IntroPredicate :<$>: MakeNode Search context (Substitute p x (X (S t))) n parents)
--         :<|>: TryIntroExists context (Exists x a p) t n parents


-- -- === TryElim === --
-- type family TryElim (flag :: Flag) (context :: [(Type, Nat)]) (conclusion :: Type) (premises :: [Type]) (n :: Nat) (parents :: [([(Type, Nat)], Type)]) :: Maybe Node where

--     TryElim flag context a (False ': premises) n parents =
--         ElimFalse
--             :<$>: MakeNode Find context False n parents
--         :<|>: TryElim flag context a premises n parents

--     TryElim flag context b ((a -> b) ': premises) n parents =
--         ElimImpl (a -> b)
--             :<$>: MakeNode Find context (a -> b) n parents
--             :<*>: MakeNode Search context a n parents
--         :<|>: TryElim flag context b premises n parents

--     TryElim flag context c ((a -> b) ': premises) n parents =
--         TryElim flag context c (b ': premises) n parents

--     TryElim flag context a ((a `And` b) ': premises) n parents =
--         ElimAndLeft (a `And` b)
--             :<$>: MakeNode Find context (a `And` b) n parents
--         :<|>: TryElim flag context a premises n parents

--     TryElim flag context b ((a `And` b) ': premises) n parents =
--         ElimAndRight (a `And` b)
--             :<$>: MakeNode Find context (a `And` b) n parents
--         -- :<|>: TryElim flag context b premises n parents

--     TryElim flag context c ((a `And` b) ': premises) n parents =
--         TryElim flag context c (a ': b ': premises) n parents  

--     TryElim Search context c ((a `Or` b) ': premises) n parents =
--         ElimOr (a `Or` b)
--             :<$>: MakeNode Find context (a `Or` b) n parents
--             :<*>: MakeNode Search (Assume a (Unassume (a `Or` b) context)) c n parents
--             :<*>: MakeNode Search (Assume b (Unassume (a `Or` b) context)) c n parents
--         :<|>: TryElim Search context c premises n parents

--     TryElim flag context p ((x :=: y) ': premises) n parents =
--         (ElimPredicate (Predicate p x x) :<$>: (ElimEq (x :=: y)
--             :<$>: MakeNode Find context (x :=: y) n parents
--             :<*>: (IntroPredicate :<$>: MakeNode Search context (Substitute p x y) n parents)))
--         :<|>: (ElimPredicate (Predicate p y y) :<$>: (ElimEq (y :=: x)
--             :<$>: (Symmetry :<$>: MakeNode Find context (x :=: y) n parents)
--             :<*>: (IntroPredicate :<$>: MakeNode Search context (Substitute p y x) n parents)))
--         :<|>: TryElim flag context p premises n parents  

--     TryElim flag context c (Forall x a p ': premises) n parents =
--         TryElimForall flag context c (Forall x a p) n n parents
--         :<|>: TryElim flag context c premises n parents

--     TryElim Search context c (Exists x a p ': premises) n parents =
--         ElimExists (Exists x a p)
--             :<$>: MakeNode Find context (Exists x a p) n parents
--             :<*>: (ElimPredicateContext (Predicate p x (X (S n)))
--                 :<$>: TryProject context (Predicate p x (X (S n)))
--                 :<*>: MakeNode Search (Assume (Substitute p x (X (S n))) (Unassume (Exists x a p) context)) c (S n) parents)
--         :<|>: TryElim Search context c premises n parents

--     TryElim flag context conclusion (premise ': premises) n parents =
--         TryElim flag context conclusion premises n parents

--     TryElim _ _ _ _ _ _ = Nothing

-- type family TryElimForall (flag :: Flag) (context :: [(Type, Nat)]) (conclusion :: Type) (premise :: Type) (target :: Nat) (n :: Nat) (parents :: [([(Type, Nat)], Type)]) :: Maybe Node where

--     TryElimForall _ _ _ _ Z _ _ = Nothing

--     TryElimForall flag context c (Forall x a p) (S t) n parents =
--         If (Equal (Substitute p x (X (S t))) c)
--             (ElimPredicate (Predicate p x (X (S t))) :<$>: (ElimForall
--                 :<$>: MakeNode Find context (Forall x a p) n parents))
--             (TryElim flag context c '[Substitute x p (X (S t))] n parents)
--         :<|>: TryElimForall flag context c (Forall x a p) t n parents

    
