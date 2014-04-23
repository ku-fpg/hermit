{-# LANGUAGE MagicHash #-}
{-# LANGUAGE CPP #-}

module Main where

import Prelude hiding ((*),(-))
import GHC.Exts

#if __GLASGOW_HASKELL__ < 708
import Data.Function (fix)
#endif

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
