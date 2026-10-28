module Search where

import Proposition
import ACFp ( F, (:+:), (:-:), (:*:), (:/:), (:^:) )
import FOL
import Utils
import Node

import Data.Kind ( Type )
import GHC.TypeLits


-- === FV X === --
data X (x :: Nat)


-- === Flag === --
data Flag = Search -- default, try to apply all inference rules
    | Find -- try to find node in context, eg. no intro rules
    | Stop -- used for loop detection


-- === MakeNode === --
type family MakeNode (flag :: Flag) (context :: [Type]) (conclusion :: Type) (parents :: [([Type], Type)]) (var :: Nat) :: Maybe Node where

    MakeNode flag context conclusion parents var =
        TryInfer
            (If (Member '(context, conclusion) parents)
                Stop
                flag)
            context
            conclusion
            (Insert '(context, conclusion) parents)
            var


-- === Try Infer === --
type family TryInfer (flag :: Flag) (context :: [Type]) (conclusion :: Type) (parents :: [([Type], Type)]) (var :: Nat) :: Maybe Node where

    TryInfer Search context conclusion parents var =
        TryProject context conclusion
        :<|>: TryIntro context conclusion parents var
        :<|>: TryElim Search context conclusion context parents var

    TryInfer Find context conclusion parents var =
        TryProject context conclusion
        :<|>: TryElim Find context conclusion context parents var

    TryInfer Stop _ _ _ _ = Nothing


-- === TryProject === --
type family TryProject (context :: [Type]) (conclusion :: Type) where

    TryProject context conclusion =
        If (Member conclusion context)
            (Just Project)
            Nothing


-- === TryIntro === --
type family TryIntro (context :: [Type]) (conclusion :: Type) (parents :: [([Type], Type)]) (var :: Nat) :: Maybe Node where

    TryIntro _ True _ _ =
        Just IntroTrue

    TryIntro context (a -> b) parents var =
        IntroImpl
            :<$>: MakeNode Search (Insert a context) b parents var

    TryIntro context (a `And` b) parents var =
        IntroAnd
            :<$>: MakeNode Search context a parents var
            :<*>: MakeNode Search context b parents var

    TryIntro context (a `Or` b) parents var =
        (IntroOrLeft
            :<$>: MakeNode Search context a parents var)
        :<|>: (IntroOrRight
            :<$>: MakeNode Search context b parents var)

    TryIntro context (a :=: a) parents var =
        Just Reflexivity

    TryIntro context (Forall x p) parents var =
        IntroForall
            :<$>: MakeNode Search context (Apply p (Var x) (X var)) parents (var + 1)

    TryIntro _ _ _ _ = Nothing

    
-- === TryElim === --
type family TryElim (flag :: Flag) (context :: [Type]) (conclusion :: Type) (premises :: [Type]) (parents :: [([Type], Type)]) (var :: Nat) :: Maybe Node where

    TryElim flag context a (False ': premises) parents var =
        ElimFalse
            :<$>: MakeNode Find context False parents var
        :<|>: TryElim flag context a premises parents var

    TryElim flag context b ((a -> b) ': premises) parents var =
        ElimImpl (a -> b)
            :<$>: MakeNode Find context (a -> b) parents var
            :<*>: MakeNode Search context a parents var
        :<|>: TryElim flag context b premises parents var

    TryElim flag context c ((a -> b) ': premises) parents var =
        TryElim flag context c (b ': premises) parents var

    TryElim flag context a ((a `And` b) ': premises) parents var =
        ElimAndLeft (a `And` b)
            :<$>: MakeNode Find context (a `And` b) parents var
        :<|>: TryElim flag context a premises parents var

    TryElim flag context b ((a `And` b) ': premises) parents var =
        ElimAndRight (a `And` b)
            :<$>: MakeNode Find context (a `And` b) parents var
        :<|>: TryElim flag context b premises parents var

    TryElim flag context c ((a `And` b) ': premises) parents var =
        TryElim flag context c (a ': b ': premises) parents var

    TryElim Search context c ((a `Or` b) ': premises) parents var =
        ElimOr (a `Or` b)
            :<$>: MakeNode Find context (a `Or` b) parents var
            :<*>: MakeNode Search (Insert a context) c parents var
            :<*>: MakeNode Search (Insert b context) c parents var
        :<|>: TryElim Search context c premises parents var

    TryElim flag context p ((x :=: y) ': premises) parents var =
        (ElimEq (x :=: y)
            :<$>: MakeNode Find context (x :=: y) parents var
            :<*>: MakeNode Search context (Apply p y x) parents var)
        :<|>: (ElimEq (y :=: x)
            :<$>: (Symmetry :<$>: MakeNode Find context (x :=: y) parents var)
            :<*>: MakeNode Search context (Apply p x y) parents var)
        :<|>: TryElim flag context p premises parents var

    TryElim flag context conclusion (premise ': premises) parents var =
        TryElim flag context conclusion premises parents var

    TryElim _ _ _ _ _ _ = Nothing
