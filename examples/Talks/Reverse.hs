module Main where

import HList
import Data.Function (fix)

{-# INLINE unwrap #-}
unwrap :: ([a] -> [a]) -> ([a] -> H a)
unwrap f = repH . f

{-# INLINE wrap #-}
wrap :: ([a] -> H a) -> ([a] -> [a])
wrap g = absH . g

{-# RULES "ww" forall f . fix f = wrap (fix (unwrap . f . wrap)) #-}

-- rev :: [a] -> [a]
rev []     = []
rev (x:xs) = rev xs ++ [x]

main :: IO ()
main = print $ length $ rev [1..15000]