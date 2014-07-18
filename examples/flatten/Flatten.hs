{-# LANGUAGE CPP #-}
module Main where

import HList

data Tree a = Node (Tree a) (Tree a) | Leaf a

flatten :: Tree a -> [a]
flatten (Leaf a)   = [a]
flatten (Node l r) = flatten l ++ flatten r

main :: IO ()
main = print (flatten (Node (Leaf 'h') (Leaf 'i')))
