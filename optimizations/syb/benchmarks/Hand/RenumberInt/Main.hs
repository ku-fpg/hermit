module Hand.RenumberInt.Main where

import Auxiliary.Auxiliary (test, applyM)
import Control.Monad.State
import Hand.RenumberInt.RenumberInt
import Auxiliary.Tree
import Auxiliary.Logic

mainTree :: IO ()
mainTree = test (putStr (show (sumTree (evalState (applyM 3 renumberInt bigTree) 0))))

mainLogic :: IO ()
mainLogic = test (putStr (flip seqLogic "done" (evalState (applyM 3 renumberIntLogic biggerLogic) 0)))
