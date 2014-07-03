module Main where

import Criterion.Main

import qualified Data.Set as Set
import Data.Set (Set)

import Prelude hiding (filter) -- because we can't get unfolding for filter

filter :: (a -> Bool) -> [a] -> [a]
filter _ [] = []
filter p (x:xs) = if p x then x : filter p xs else filter p xs

nub :: [Int] -> [Int]
nub [] = []
nub (x:xs) = x : nub (filter (/= x) xs)

absN :: ([Int] -> Set Int -> [Int]) -> [Int] -> [Int]
absN h [] = []
absN h (x:xs) = x : h xs (Set.singleton x)

repN :: ([Int] -> [Int]) -> [Int] -> Set Int -> [Int]
repN h xs s = h (filter (`Set.notMember` s) xs)

--main = print (nub [ x | n <- [1..1000], x <- [1..n] ])
main = defaultMain
        [ bench (show sz) $ nf nub [ x | n <- [1..sz], x <- [1..n] ]
        | sz <- take 2 [100,200..]
        ]

{-# RULES "filter-fusion" [~] forall p q ys. filter p (filter q ys) = filter (\y -> p y && q y) ys #-}
{-# RULES "member-fusion" [~] forall y x s. (y /= x) && (y `Set.notMember` s) = y `Set.notMember` (Set.insert x s) #-}
