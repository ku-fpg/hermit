module Main where

import Data.Function (fix)

-- {-# RULES "x" hermit () = fix #-}

rev []     = []
rev (x:xs) = rev xs ++ [x]

--hermit :: () -> a
--hermit = undefined

f g = let x = g x in x

main = print (rev "Hello, World")
{-
import Prelude hiding (reverse)

{-# RULES "append-assoc-left" forall xs ys zs . (xs ++ ys) ++ zs = xs ++ (ys ++ zs) #-}

main = print (reverse "Hello, World")

reverse []     = []
reverse (x:xs) = reverse xs ++ [x]

test :: [Int]
test = ([1] ++ [2]) ++ [3]


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

-}