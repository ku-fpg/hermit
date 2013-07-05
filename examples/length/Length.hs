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
rep n acc = n + acc

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
  n + 0 == n
<=>
  n == n
<=>
  True
-}


{-# RULES "rep-distr" forall m n. rep (m + n) = rep m . rep n #-}
{-
  rep (m + n) == rep m . rep n
<=>
  rep (m + n) acc == rep m (rep n) acc


  rep (m + n) acc
=
  m + n + acc
=
  rep m (n + acc)
=
  rep m (rep n acc)
-}