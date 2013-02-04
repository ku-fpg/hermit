module Main where

import HList
import Data.Function (fix)
import Data.List

data Tree a = Node (Tree a) (Tree a) | Leaf a

unwrap :: ([a] -> [a]) -> ([a] -> H a)
unwrap f = repH . f

wrap :: ([a] -> H a) -> ([a] -> [a])
wrap g = absH . g

qsort :: Ord a => [a] -> [a]
qsort []     = []
qsort (a:as) = qsort bs ++ [a] ++ qsort cs
               where
                  (bs , cs) = partition (< a) as

main :: IO ()
main = print (qsort [8,3,5,7,2,9,4,6,3,2])

