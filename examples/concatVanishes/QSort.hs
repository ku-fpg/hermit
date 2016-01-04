{-# LANGUAGE CPP #-}
module Main where

import HList
import Data.List

data Tree a = Node (Tree a) (Tree a) | Leaf a

qsort        :: Ord a => [a] -> [a]
qsort []     = []
qsort (a:as) = qsort bs ++ [a] ++ qsort cs
               where
                  (bs , cs) = partition (< a) as

main :: IO ()
main = print (qsort [8,3,5,7,2,9,4,6,3,2])

-- Should be in the "List" module
{-# RULES "++ []"  forall xs .  xs ++ [] = xs #-}
{-# RULES "++ strict"           (++) undefined = undefined #-}

-- The "Algebra" for repH
{-# RULES "repH ++" forall xs ys .     repH (xs ++ ys) = repH xs . repH ys #-}
{-# RULES "repH []"                    repH [] = id                        #-}
{-# RULES "repH (:)" forall x xs .     repH (x:xs) = ((:) x) . repH xs     #-}
