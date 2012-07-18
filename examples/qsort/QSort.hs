module Main where

import HList
import Data.Function (fix)
import Data.List

data Tree a = Node (Tree a) (Tree a) | Leaf a

{-# INLINE unwrap #-}
unwrap :: ([a] -> [a]) -> ([a] -> H a)
unwrap f = repH . f

{-# INLINE wrap #-}
wrap :: ([a] -> H a) -> ([a] -> [a])
wrap g = absH . g

{-# RULES "ww" forall f . fix f = wrap (fix (unwrap . f . wrap)) #-}
{-# RULES "inline-fix" forall f . fix f = let w = f w in w #-}

-- qsort :: Ord a => [a] -> [a]
qsort []     = []
qsort (a:as) = qsort bs ++ [a] ++ qsort cs
               where
                  (bs , cs) = partition (< a) as

main :: IO ()
main = print (qsort [8,3,5,7,2,9,4,6,3,2])

