{-# LANGUAGE CPP #-}
module Main where

import HList

#if __GLASGOW_HASKELL__ < 708
import Data.Function (fix)
#endif

rev :: [a] -> [a]
rev []     = []
rev (y:ys) = rev ys ++ [y]

main :: IO ()
main = print $ rev [1..10]

