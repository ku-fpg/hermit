module SYB.Map.Main where

import Auxiliary.Tree (smallerTree, sumTree, Tree)
import Auxiliary.Auxiliary (test, apply)
import Auxiliary.SYB

import Data.Generics

import HERMIT.Optimization.SYB.Prelude

mainTree :: IO ()
mainTree = test (putStr (show (sumTree (apply 1000 (incTree (+1)) smallerTree))))

incTree :: (Int -> Int) -> (Tree Int -> Tree Int)
incTree f = everywhere (mkT f)
