{-# LANGUAGE CPP #-}
module Main where

import HList
-- import Seq

#if __GLASGOW_HASKELL__ < 708
import Data.Function (fix)
#endif

rev :: [a] -> [a]
rev []     = []
rev (x:xs) = rev xs ++ [x]

main :: IO ()
main = print $ rev "hello"
