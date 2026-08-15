module Search where

import Proposition
import Utils
import Node

import Data.Kind ( Type )


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

    TryIntro _ _ _ = Nothing

    
-- === TryElim === --
type family TryElim (flag :: Flag) (context :: [Type]) (conclusion :: Type) (premises :: [Type]) (parents :: [([Type], Type)]) :: Maybe Node where

    TryElim flag context a (False ': premises) parents =
        ElimFalse
            :<$>: MakeNode Find context False parents
        :<|>: TryElim flag context a premises parents

    TryElim flag context b ((a -> b) ': premises) parents =
        ElimImpl (a -> b)
            :<$>: MakeNode Find context (a -> b) parents
            :<*>: MakeNode Search context a parents
        :<|>: TryElim flag context b premises parents

    TryElim flag context c ((a -> b) ': premises) parents =
        TryElim flag context c '[b] parents
        :<|>: TryElim flag context c premises parents

    TryElim flag context a ((a `And` b) ': premises) parents =
        ElimAndLeft (a `And` b)
            :<$>: MakeNode Find context (a `And` b) parents
        :<|>: TryElim flag context a premises parents

    TryElim flag context b ((a `And` b) ': premises) parents =
        ElimAndRight (a `And` b)
            :<$>: MakeNode Find context (a `And` b) parents
        :<|>: TryElim flag context b premises parents

    TryElim flag context c ((a `And` b) ': premises) parents =
        TryElim flag context c '[a] parents
        :<|>: TryElim flag context c '[b] parents
        :<|>: TryElim flag context c premises parents

    TryElim Search context c ((a `Or` b) ': premises) parents =
        ElimOr (a `Or` b)
            :<$>: MakeNode Find context (a `Or` b) parents
            :<*>: MakeNode Search (Insert a context) c parents
            :<*>: MakeNode Search (Insert b context) c parents
        :<|>: TryElim Search context c premises parents

    TryElim flag context conclusion (premise ': premises) parents =
        TryElim flag context conclusion premises parents

    TryElim _ _ _ _ _ = Nothing
