module Interactive where

import Utils
import Node
import Search
import Inference
import Tactics

import Data.HList ( HList(..) )
import Data.Kind ( Type )

import Prelude hiding ( interact )


-- === Prove === --
prove :: Tactic a () () -> a
prove (Tactic f) = f (\() -> ())


-- === Experiments === --
-- interactive :: IO a
-- interactive = do
--     a <- loop HNil
--     return $ prove a

-- loop :: HList ls -> IO (Tactic a () ())
-- loop ls = do
--     input <- getLine
--     case input of
--         "q" -> return qed
