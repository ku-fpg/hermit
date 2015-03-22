module Main where

import HList
import Data.Function (fix)

{-# INLINE repR #-}
repR :: ([a] -> [a]) -> ([a] -> H a)
repR f = repH . f

{-# INLINE absR #-}
absR :: ([a] -> H a) -> ([a] -> [a])
absR g = absH . g

rev :: [a] -> [a]
rev []     = []
rev (x:xs) = rev xs ++ [x]

main :: IO ()
main = print $ rev [1..10]

-- useful auxilliary lemma for proving the w/w assumption
{-# RULES "++ []" [~] forall xs. xs ++ [] = xs #-}
{-# RULES "myAppend-assoc" [~] forall xs ys zs. myAppend (myAppend xs ys) zs = myAppend xs (myAppend ys zs) #-}
