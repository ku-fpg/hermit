module Main where

import HList

rev :: [a] -> [a]
rev []     = []
rev (x:xs) = rev xs ++ [x]

main :: IO ()
main = print $ rev "hello"
