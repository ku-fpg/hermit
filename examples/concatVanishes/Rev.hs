{-# LANGUAGE CPP #-}
module Main where

import HList

rev :: [a] -> [a]
rev []     = []
rev (y:ys) = rev ys ++ [y]

main :: IO ()
main = print $ rev [1..10]

