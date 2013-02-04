module Main where

import HList
import Data.Function (fix)

unwrap :: ([a] -> [a]) -> ([a] -> H a)
unwrap f = repH . f

wrap :: ([a] -> H a) -> ([a] -> [a])
wrap g = absH . g

rev :: [a] -> [a]
rev []     = []
rev (y:ys) = rev ys ++ [y]

main :: IO ()
main = print $ rev [1..10]

