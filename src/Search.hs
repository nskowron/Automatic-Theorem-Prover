module Search where

import Proposition
import ACFp ( F, (:+:), (:-:), (:*:), (:/:), (:^:) )
import FOL
import Utils
import Node

import Data.Kind ( Type )
import GHC.TypeLits ( Symbol )


-- === Variables === --
data All (x :: Symbol) (a :: d -> Type)
data Any (x :: Symbol) (a :: d -> Type)

type family Dequantify p where

    Dequantify (a -> b) = Dequantify a -> Dequantify b
    Dequantify (a `And` b) = Dequantify a `And` Dequantify b
    Dequantify (a `Or` b) = Dequantify a `Or` Dequantify b

    Dequantify (a :=: b) = Dequantify a :=: Dequantify b
    
    Dequantify (Forall x a p) = Forall x a (Dequantify p)
    Dequantify (Exists x a p) = Exists x a (Dequantify p)

    Dequantify (a :+: b) = Dequantify a :+: Dequantify b
    Dequantify (a :-: b) = Dequantify a :-: Dequantify b
    Dequantify (a :*: b) = Dequantify a :*: Dequantify b
    Dequantify (a :/: b) = Dequantify a :/: Dequantify b
    Dequantify (a :^: b) = Dequantify a :^: Dequantify b

    Dequantify (All x a) = Var x
    Dequantify (Any x a) = Var x

    Dequantify p = p


-- === Flag === --
data Flag = Search -- default, try to apply all inference rules
    | Find -- try to find node in context, eg. no intro rules
    | Stop -- used for loop detection


-- === MakeNode === --
type family MakeNode (flag :: Flag) (context :: [Type]) (conclusion :: Type) (parents :: [([Type], Type)]) :: Maybe Node where

    MakeNode flag context conclusion parents =
        TryInfer
            (If (Member '(context, conclusion) parents)
                Stop
                flag)
            context
            conclusion
            (Insert '(context, conclusion) parents)


-- === Try Infer === --
type family TryInfer (flag :: Flag) (context :: [Type]) (conclusion :: Type) (parents :: [([Type], Type)]) :: Maybe Node where

    TryInfer Search context (a :=: b) parents =
        TryProject context (a :=: b)
        :<|>: TryIntro context (a :=: b) parents
        :<|>: TryElim Search context (a :=: b) context parents
        :<|>: TryElim Search context (b :=: a) context parents

    TryInfer Search context conclusion parents =
        TryProject context conclusion
        :<|>: TryIntro context conclusion parents
        :<|>: TryElim Search context conclusion context parents

    TryInfer Find context conclusion parents =
        TryProject context conclusion
        :<|>: TryElim Find context conclusion context parents

    TryInfer Stop _ _ _ = Nothing


-- === TryProject === --
type family TryProject (context :: [Type]) (conclusion :: Type) where

    TryProject context conclusion =
        If (Member conclusion context)
            (Just Project)
            Nothing


-- === TryIntro === --
type family TryIntro (context :: [Type]) (conclusion :: Type) (parents :: [([Type], Type)]) :: Maybe Node where

    TryIntro _ True _ =
        Just IntroTrue

    TryIntro context (a -> b) parents =
        IntroImpl
            :<$>: MakeNode Search (Insert a context) b parents

    TryIntro context (a `And` b) parents =
        IntroAnd
            :<$>: MakeNode Search context a parents
            :<*>: MakeNode Search context b parents

    TryIntro context (a `Or` b) parents =
        (IntroOrLeft
            :<$>: MakeNode Search context a parents)
        :<|>: (IntroOrRight
            :<$>: MakeNode Search context b parents)

    TryIntro context (a :=: a) parents =
        Just Reflexivity

    TryIntro context (Forall x a p) parents =
        IntroForall
            :<$>: MakeNode Search context (Eval (Apply p '[ '(x, All x a)])) parents

    -- TryIntro context (Exists Type p) parents =
    --     (IntroExists True
    --         :<$>: MakeNode Search context (Predicate p True) parents)
    --     :<|>: (IntroExists False
    --         :<$>: MakeNode Search context (Predicate p False) parents)

    TryIntro _ _ _ = Nothing

    
-- === TryElim === --
type family TryElim (flag :: Flag) (context :: [Type]) (conclusion :: Type) (premises :: [Type]) (parents :: [([Type], Type)]) :: Maybe Node where

    TryElim flag context a (False ': premises) parents =
        ElimFalse
            :<$>: MakeNode Find context False parents
        :<|>: TryElim flag context a premises parents

    TryElim flag context b ((a -> b) ': premises) parents =
        ElimImpl (Dequantify (a -> b))
            :<$>: MakeNode Find context (a -> b) parents
            :<*>: MakeNode Search context a parents
        :<|>: TryElim flag context b premises parents

    TryElim flag context c ((a -> b) ': premises) parents =
        TryElim flag context c (b ': premises) parents

    TryElim flag context a ((a `And` b) ': premises) parents =
        ElimAndLeft (Dequantify (a `And` b))
            :<$>: MakeNode Find context (a `And` b) parents
        :<|>: TryElim flag context a premises parents

    TryElim flag context b ((a `And` b) ': premises) parents =
        ElimAndRight (Dequantify (a `And` b))
            :<$>: MakeNode Find context (a `And` b) parents
        :<|>: TryElim flag context b premises parents

    TryElim flag context c ((a `And` b) ': premises) parents =
        TryElim flag context c (a ': b ': premises) parents

    TryElim Search context c ((a `Or` b) ': premises) parents =
        ElimOr (Dequantify (a `Or` b))
            :<$>: MakeNode Find context (a `Or` b) parents
            :<*>: MakeNode Search (Insert a context) c parents
            :<*>: MakeNode Search (Insert b context) c parents
        :<|>: TryElim Search context c premises parents

    TryElim flag context p ((x :=: y) ': premises) parents =
        (ElimEq (Dequantify (x :=: y)) (Dequantify p)
            :<$>: MakeNode Find context (x :=: y) parents
            :<*>: MakeNode Search context (Replace p y x) parents)
        :<|>: (ElimEq (Dequantify (y :=: x)) (Dequantify p)
            :<$>: (Symmetry :<$>: MakeNode Find context (x :=: y) parents)
            :<*>: MakeNode Search context (Replace p x y) parents)

    -- TryElim flag context (a :=: b) ((b :=: c) ': premises) parents =
    --     MakeNode Search context (a :=: c) parents
    --     :<|>: TryElim Search context (a :=: b) premises parents

    TryElim flag context conclusion (premise ': premises) parents =
        TryElim flag context conclusion premises parents

    TryElim _ _ _ _ _ = Nothing
