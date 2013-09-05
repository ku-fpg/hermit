module Main where

import Prelude hiding (length,abs)

import Data.Function (fix)
import GHC.Err (undefined)

length :: [a] -> Int
length []     = zero
length (a:as) = length as + 1

main :: IO ()
main = print (length [1..1000000])

-- Goal
-- length :: [a] -> Int
-- length as = work as 0
--   where
--     work []     acc = acc
--     work (b:bs) acc = acc `seq` work bs (1 + acc)

-- This definition, despite being tail recursive, still stack overflows.
-- The addition of the "seq" is crucial.
-- length' :: [a] -> Int
-- length' as = work as zero
--   where
--     work []     acc = acc
--     work (b:bs) acc = work bs (1 + acc)

rep :: Int -> Int -> Int
rep n = (n +)

abs :: (Int -> Int) -> Int
abs f = f zero

{-# NOINLINE zero #-}
zero :: Int
zero = 0

{-# RULES "+ zero" forall n. n + zero = n #-}
{-# RULES "zero +" forall n. zero + n = n #-}
{-# RULES "assocLtoR" forall l m n. (l + m) + n = l + (m + n) #-}
