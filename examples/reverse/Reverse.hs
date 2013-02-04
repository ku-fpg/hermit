module Main where

import HList
import Data.Function (fix)

unwrap :: ([a] -> [a]) -> ([a] -> H a)
unwrap f = repH . f

wrap :: ([a] -> H a) -> ([a] -> [a])
wrap g = absH . g

rev :: [a] -> [a]
rev []     = []
rev (x:xs) = rev xs ++ [x]

main :: IO ()
main = print $ rev "hello"
