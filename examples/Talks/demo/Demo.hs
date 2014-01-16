module Demo where

--------------------------------------------

-- Part 1

f :: Bool -> Bool -> Int
f a b = g a (if b then True else b && True)

--------------------------------------------

-- Part 2

g :: Bool -> Bool -> Int
g a True  = 1
g a False = g False True

{-# RULES "strict-ga" [1]  forall a.  g a undefined = undefined  #-}

--------------------------------------------
