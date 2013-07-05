module Main (main,wrap,unwrap) where

import Prelude hiding (length,abs)

import Data.Function (fix)

length :: [a] -> Int
length []     = 0
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
length' :: [a] -> Int
length' as = work as 0
  where
    work []     acc = acc
    work (b:bs) acc = work bs (1 + acc)

unwrap :: ([a] -> Int) -> [a] -> Int -> Int
unwrap l = rep . l

wrap :: ([a] -> Int -> Int) -> [a] -> Int
wrap l = abs . l

rep :: Int -> Int -> Int
rep n acc = acc `seq` (n + acc)

abs :: (Int -> Int) -> Int
abs f = f 0

{-
Assumption A

  abs . rep == id
<=>
  abs (rep n) == n
<=>
  rep n 0 == n
<=>
  0 `seq` (n + 0) == n
<=>
  n + 0 == n
<=>
  n == n
<=>
  True
-}


{-# RULES "rep-distr" forall m n acc. rep (m + n) acc = acc `seq` (rep m acc + n) #-}
{-
  rep (m + n) acc
=
  acc `seq` (m + n + acc)
=
  acc `seq` (m + acc + n)
=
  acc `seq` ((acc `seq` (m + acc)) + n)
=
  acc `seq` (rep m acc + n)
-}