module Main where

import Prelude hiding (reverse)

main = print (reverse "Hello, World")

reverse []     = []
reverse (x:xs) = reverse xs ++ [x]

foo :: Int -> Bool -> Float -> Int
foo a b c = f (x + y + z)
  where
     {-# NOINLINE x #-}
     x = 1
     {-# NOINLINE y #-}
     y = 2
     {-# NOINLINE z #-}
     z = 3 + a
     {-# NOINLINE f #-}
     f x = x + 1