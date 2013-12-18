module Main where

import Prelude hiding ((++))

{-# RULES "++ []" forall xs.  xs ++ [] = xs #-}

(++) :: [a] -> [a] -> [a]
[]     ++ bs = bs
(a:as) ++ bs = a : (as ++ bs)

main :: IO ()
main = print (replicate 5 True ++ [])
