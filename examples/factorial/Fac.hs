{-# LANGUAGE MagicHash #-}

module Main where

import Prelude hiding ((*),(-))
import GHC.Exts
import Data.Function(fix)

------------------------------------

fac :: Int -> Int
fac 0 = 1
fac n = n * fac (n -1)

unwrap :: (Int -> Int) -> Int# -> Int#
unwrap h x = case h (I# x) of
               I# y -> y

wrap :: (Int# -> Int#) -> Int -> Int
wrap h (I# x) = I# (h x)

main :: IO ()
main = print (fac 10)


(*) :: Int -> Int -> Int
(I# x) * (I# y) = I# (x *# y)

(-) :: Int -> Int -> Int
(I# x) - (I# y) = I# (x -# y)

------------------------------------

-- f :: (Int -> Int) -> (Int -> Int)
-- f _ 0 = 1
-- f h n = n * h (n -1)

-- proof = \ h -> wrap (unwrap (f h))

------------------------------------
