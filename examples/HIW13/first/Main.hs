module Main where

import Data.List (map)

foo :: [Int] -> Int
foo = foldl (+) 0 . map (+1)

bar :: [Int] -> [Int]
bar = map (*2)

main :: IO ()
main = print $ foo . bar $ [1..10]

{-# RULES "map/map" [~] forall f g xs. map f (map g xs) = map (f . g) xs #-}
