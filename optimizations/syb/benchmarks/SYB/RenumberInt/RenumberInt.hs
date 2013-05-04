module SYB.RenumberInt.RenumberInt where

import Data.Generics
import Control.Monad.State

getUnique :: Int -> State Int Int
getUnique _ = do
    u <- get
    modify (+1)
    return u

renumberInt :: Data a => a -> State Int a
renumberInt = everywhereM (mkM getUnique)
