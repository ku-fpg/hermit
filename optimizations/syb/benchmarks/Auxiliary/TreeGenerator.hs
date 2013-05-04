{-# OPTIONS -XDeriveDataTypeable #-}

module Main where

import System.Random
import Data.Generics

data Tree a = Bin a (Tree a) (Tree a) | Leaf deriving (Show, Data, Typeable)

genTree :: [Int] -> Tree Int
genTree []    = Leaf
genTree [_]   = Leaf
genTree (h:t@(_:_)) | even h = Bin h (genTree t) (genTree (tail t))
                    | odd h  = Bin h (genTree (tail t)) (genTree t)

main :: IO ()
main = getStdGen >>= writeFile "outTree" . gshow . genTree . take 24 . randomRs (0,100)
