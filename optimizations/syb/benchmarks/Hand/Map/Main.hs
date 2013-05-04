module Hand.Map.Main where

import Auxiliary.Tree (smallerTree, sumTree, mapTree, Tree(..))
import Auxiliary.Auxiliary (test, apply)

mainTree :: IO ()
mainTree = test (putStr (show (sumTree (apply 1000 (mapTree (+1)) smallerTree))))

