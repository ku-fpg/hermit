module Main where

import Data.Function(fix)
import Prelude hiding (abs, map)

data List2 a = Cons2 a a (List2 a)
             | Singleton a
             | Nil

rep :: [a] -> List2 a
rep []       = Nil
rep [x]      = Singleton x
rep (x:y:xs) = Cons2 x y (rep xs)

abs :: List2 a -> [a]
abs Nil            = []
abs (Singleton x)  = [x]
abs (Cons2 x y xs) = x : y : abs xs

unwrap :: ([a] -> [b]) -> (List2 a -> List2 b)
unwrap f = rep . f . abs

wrap :: (List2 a -> List2 b) -> ([a] -> [b])
wrap f = abs . f . rep

-- needed for WWSplitTactic.hss
{-# RULES "ww" forall f . fix f = wrap (fix (unwrap . f . wrap)) #-}
{-# RULES "inline-fix" forall f . fix f = let work = f work in work #-}
{-# RULES "precondition1" forall xs . abs (rep xs) = xs #-}
{-# RULES "precondition2" forall xs . rep (abs xs) = xs #-}

-- can apply "ww" rule to this
mapPlus1Int :: [Int] -> [Int]
mapPlus1Int []     = []
mapPlus1Int (x:xs) = (x+1) : mapPlus1Int xs

{- can't apply "ww" rule to either of these... is it because of the forall type?
unwrap :: ((a -> b) -> [a] -> [b]) -> ((a -> b) -> [a] -> List2 b)
unwrap g f = rep . g f

wrap :: ((a -> b) -> [a] -> List2 b) -> ((a -> b) -> [a] -> [b])
wrap g f = abs . g f
-}
mapPlus1 :: Num a => [a] -> [a]
mapPlus1 []     = []
mapPlus1 (x:xs) = (x+1) : mapPlus1 xs

map :: (a -> b) -> [a] -> [b]
map _ []     = []
map f (x:xs) = f x : map f xs

main :: IO ()
main = print (map (+1) [1..10::Int])
