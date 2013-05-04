module Hand.Update.Main where

import Auxiliary.Tree (bigTree, sumTree)
import Auxiliary.Logic (biggerLogic, evalLogic)
import Auxiliary.Auxiliary (test, apply)
import Hand.Update.Update

mainTree :: IO ()
mainTree = test . putStr . show . sumTree . (apply 20 updateTree) $ bigTree

mainLogic :: IO ()
mainLogic = test . putStr . show . evalLogic (\_ _ -> True) . (apply 800 (updateLogic (const 'y'))) $ biggerLogic
