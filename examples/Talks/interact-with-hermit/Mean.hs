module Main (main, mean) where

import Prelude hiding (sum, length)

mean :: [Int] -> Int
mean xs = sum xs `div` length xs

sum :: [Int] -> Int
sum []     = 0
sum (x:xs) = x + sum xs

length :: [Int] -> Int
length []     = 0
length (x:xs) = 1 + length xs

main :: IO ()
main = print $ mean [1..10]
