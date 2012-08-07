module Main where

import Criterion.Main
import HList
import Data.Function (fix)

{-# INLINE unwrap #-}
unwrap :: ([a] -> [a]) -> ([a] -> H a)
unwrap f = repH . f

{-# INLINE wrap #-}
wrap :: ([a] -> H a) -> ([a] -> [a])
wrap g = absH . g

{-# RULES "ww" forall f . fix f = wrap (fix (unwrap . f . wrap)) #-}
{-# RULES "inline-fix" forall f . fix f = let w = f w in w #-}

-- rev :: [a] -> [a]
rev []     = []
rev (x:xs) = rev xs ++ [x]

main = defaultMain
       [ bench (show n) $ whnf (\n -> sum $ rev [1..n]) n
       | n <- take 8 $ [50,100..]
       ]
