module Search where

import Proposition
import ACFp ( F, (:+:), (:-:), (:*:), (:/:), (:^:) )
import FOL
import Utils
import Node

import Data.Kind ( Type )
import GHC.TypeLits


-- === FV X === --
data X (n :: Nat)

type family Apply p env where

    Apply (X n) ('(n, v) ': _) = v
    Apply (X n) ('(m, _) ': env) = Apply (X n) env

    Apply (a -> b) env = Apply a env -> Apply b env
    Apply (a `And` b) env = Apply a env `And` Apply b env
    Apply (a `Or` b) env = Apply a env `Or` Apply b env

    Apply (a :=: b) env = Apply a env :=: Apply b env
    
    Apply (Forall x p) env = Forall x (Apply p env)
    Apply (Exists x p) env = Exists x (Apply p env)

    Apply p env = p


-- === Flag === --
data Flag = Search -- default, try to apply all inference rules
    | Find -- try to find node in context, eg. no intro rules
    | Stop -- used for loop detection


-- === MakeNode === --
type family MakeNode (flag :: Flag) (context :: [Type]) (conclusion :: Type) (parents :: [([Type], Type)]) (env :: [(Nat, Type)]) :: Maybe Node where

    MakeNode flag context conclusion parents env =
        TryInfer
            (If (Member '(context, conclusion) parents)
                Stop
                flag)
            context
            conclusion
            (Insert '(context, conclusion) parents)
            env


-- === Try Infer === --
type family TryInfer (flag :: Flag) (context :: [Type]) (conclusion :: Type) (parents :: [([Type], Type)]) (env :: [(Nat, Type)]) :: Maybe Node where

    TryInfer Search context (a -> b) parents env =
        TryIntro context (a -> b) parents env

    TryInfer Search context (Forall x p) parents env =
        TryIntro context (Forall x p) parents env

    TryInfer Search context (a `And` b) parents env =
        TryIntro context (a `And` b) parents env

    TryInfer Search context (Exists x p) parents env =
        TryProject context (Exists x p)
        :<|>: TryElim Search context (Exists x p) context parents env
        :<|>: TryIntro context (Exists x p) parents env

    TryInfer Search context conclusion parents env =
        TryProject context conclusion
        :<|>: TryIntro context conclusion parents env
        :<|>: TryElim Search context conclusion context parents env

    TryInfer Find context conclusion parents env =
        TryProject context conclusion
        :<|>: TryElim Find context conclusion context parents env

    TryInfer Stop _ _ _ _ = Nothing


-- === TryProject === --
type family TryProject (context :: [Type]) (conclusion :: Type) where

    TryProject context conclusion =
        If (Member conclusion context)
            (Just Project)
            Nothing


-- === TryIntro === --
type family TryIntro (context :: [Type]) (conclusion :: Type) (parents :: [([Type], Type)]) (env :: [(Nat, Type)]) :: Maybe Node where

    TryIntro _ True _ _ =
        Just IntroTrue

    TryIntro context (a -> b) parents env =
        IntroImpl
            :<$>: MakeNode Search (Insert a context) b parents env

    TryIntro context (a `And` b) parents env =
        IntroAnd
            :<$>: MakeNode Search context a parents env
            :<*>: MakeNode Search context b parents env

    TryIntro context (a `Or` b) parents env =
        (IntroOrLeft
            :<$>: MakeNode Search context a parents env)
        :<|>: (IntroOrRight
            :<$>: MakeNode Search context b parents env)

    TryIntro context (a :=: a) parents env =
        Just Reflexivity

    TryIntro context (Forall x p) parents ('(n, v) ': env) =
        IntroForall
            :<$>: MakeNode Search context (Substitute p (Var x) (X (n + 1))) parents ('(n + 1, Var x) ': '(n, v) ': env)

    TryIntro context (Exists x p) parents ('(n, v) ': env) =
        TryIntroExists context (Exists x p) n parents ('(n, v) ': env)

    TryIntro _ _ _ _ = Nothing

    
-- === TryIntroExists === --
type family TryIntroExists (context :: [Type]) (conclusion :: Type) (n :: Nat) (parents :: [([Type], Type)]) (env :: [(Nat, Type)]) :: Maybe Node where

    TryIntroExists _ _ 0 _ _ = Nothing

    TryIntroExists context (Exists x p) n parents env =
        IntroExists (Apply (X n) env)
            :<$>: MakeNode Find context (Substitute p (Var x) (X n)) parents env
        :<|>: TryIntroExists context (Exists x p) (n - 1) parents env


-- === TryElim === --
type family TryElim (flag :: Flag) (context :: [Type]) (conclusion :: Type) (premises :: [Type]) (parents :: [([Type], Type)]) (env :: [(Nat, Type)]) :: Maybe Node where

    TryElim flag context a (False ': premises) parents env =
        ElimFalse
            :<$>: MakeNode Find context False parents env
        :<|>: TryElim flag context a premises parents env

    TryElim flag context b ((a -> b) ': premises) parents env =
        ElimImpl (Apply (a -> b) env)
            :<$>: MakeNode Find context (a -> b) parents env
            :<*>: MakeNode Search context a parents env
        :<|>: TryElim flag context b premises parents env

    TryElim flag context c ((a -> b) ': premises) parents env =
        TryElim flag context c (b ': premises) parents env

    TryElim flag context a ((a `And` b) ': premises) parents env =
        ElimAndLeft (Apply (a `And` b) env)
            :<$>: MakeNode Find context (a `And` b) parents env
        :<|>: TryElim flag context a premises parents env

    TryElim flag context b ((a `And` b) ': premises) parents env =
        ElimAndRight (Apply (a `And` b) env)
            :<$>: MakeNode Find context (a `And` b) parents env
        :<|>: TryElim flag context b premises parents env

    TryElim flag context c ((a `And` b) ': premises) parents env =
        TryElim flag context c (a ': b ': premises) parents env

    TryElim Search context c ((a `Or` b) ': premises) parents env =
        ElimOr (Apply (a `Or` b) env)
            :<$>: MakeNode Find context (a `Or` b) parents env
            :<*>: MakeNode Search (Insert a context) c parents env
            :<*>: MakeNode Search (Insert b context) c parents env
        :<|>: TryElim Search context c premises parents env

    TryElim flag context p ((x :=: y) ': premises) parents env =
        (ElimEq (Apply (x :=: y) env)
            :<$>: MakeNode Find context (x :=: y) parents env
            :<*>: MakeNode Search context (Substitute p y x) parents env)
        :<|>: (ElimEq (Apply (y :=: x) env)
            :<$>: (Symmetry :<$>: MakeNode Find context (x :=: y) parents env)
            :<*>: MakeNode Search context (Substitute p x y) parents env)
        :<|>: TryElim flag context p premises parents env

    TryElim Search context c ((Exists x p) ': premises) parents ('(n, v) ': env) =
        ElimExists (Apply (Exists x p) ('(n, v) ': env))
            :<$>: MakeNode Find context (Exists x p) parents ('(n, v) ': env)
            :<*>: MakeNode Search (Substitute p (Var x) (X (n + 1)) ': Remove (Exists x p) context) c parents ('(n + 1, Var x) ': '(n, v) ': env)
        :<|>: TryElim Search context c premises parents ('(n, v) ': env)

    TryElim flag context conclusion (premise ': premises) parents env =
        TryElim flag context conclusion premises parents env

    TryElim _ _ _ _ _ _ = Nothing
