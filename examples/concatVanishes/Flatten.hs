{-# LANGUAGE CPP #-}
module Main where

import HList

#if __GLASGOW_HASKELL__ < 708
import Data.Function (fix)
#endif

data Tree a = Node (Tree a) (Tree a) | Leaf a

flatten :: Tree a -> [a]
flatten (Leaf a)   = [a]
flatten (Node l r) = flatten l ++ flatten r

main :: IO ()
main = print (flatten (Node (Leaf 'h') (Leaf 'i')))
