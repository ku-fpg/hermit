module Main where

import Criterion.Main
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

main = defaultMain
       [ bench (show n) $ whnf (\n -> sum $ rev [1..n]) n
       | n <- take 8 $ [50,100..]
       ]

-- useful auxilliary lemma for proving the w/w assumption
{-# RULES "++ []" [~] forall xs. xs ++ [] = xs #-}
