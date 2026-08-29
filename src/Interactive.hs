module Interactive where

import Utils
import Node
import Search

import Data.Kind ( Type )

import Prelude hiding ( interact )


class Interactive proposition where
    interact :: IO proposition

instance
    ( Loop Unprovable proposition
    ) => Interactive proposition where
    interact = loop @Unprovable @proposition

class Loop (node :: Node) (proposition :: Type) where
    loop :: IO proposition

instance
    ( ShowType '(node, proposition)
    , Loop (FromMaybe Unprovable (MakeNode Search '[] proposition '[])) proposition
    ) => Loop node proposition where
    loop = do
        putStrLn $ showType @'(node, proposition)
        input <- getLine

        case input of
            "prove" -> loop @(FromMaybe Unprovable (MakeNode Search '[] proposition '[])) @proposition
            _ -> loop @node @proposition
