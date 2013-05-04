module SYB.RenumberInt.Main where

import Auxiliary.Auxiliary (test, apply, applyM)
import SYB.RenumberInt.RenumberInt
import Auxiliary.Tree
import Auxiliary.Logic
import Auxiliary.SYB
import Control.Monad.State

import HERMIT.Optimization.SYB.Prelude

mainTree :: IO ()
mainTree = test (putStr (show (sumTree (evalState (applyM 3 renumberInt bigTree) 0))))
-- mainTree = test (putStr (show (sumTree (fst (apply 3 (\(t,s) -> runState (renumberInt t) s) (bigTree, 0))))))

mainLogic :: IO ()
mainLogic = test (putStr (flip seqLogic "done" (evalState (applyM 3 renumberInt biggerLogic) 0)))

