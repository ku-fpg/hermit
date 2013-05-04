module SYB.SelectInt.Main where

import Auxiliary.Auxiliary (test, apply)
import SYB.SelectInt.SelectInt
import TreeDatatype

import HERMIT.Optimization.SYB.Prelude

mainWTree :: IO ()
{-
mainWTree = do
    mapM_ (\n -> let s = sizeWTree (mkFullWTree n)
                 in putStrLn $ show n ++ ": " ++ show s) [65,67..]
-}
mainWTree = test (putStr (show (sumWTree (apply 30 (\t -> sum (selectInt_acc t) `seq` t) (mkFullWTree 53)))))
