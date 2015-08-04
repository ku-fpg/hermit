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


{-# RULES "appendFix" [~] (++) = myAppend #-}

-- Algebra for repH
{-# RULES "repH []"  [~]               repH [] = id #-}
{-# RULES "repH (:)" [~] forall x xs.  repH (x:xs) = (x:) . repH xs #-}
{-# RULES "repH ++"  [~] forall xs ys. repH (xs ++ ys) = repH xs . repH ys #-}

-- Needed because the fusion rule we generate isn't too useful yet.
{-# RULES "repH-absH-fusion" [~] forall h. repH (absH h) = h #-}

