module Main where

main = print "Test"

beta_reduce_start :: Int
beta_reduce_start = f 1
  where
        f = \ x -> x + 2 :: Int -- is auto-inlined

beta_reduce_end :: Int
beta_reduce_end = 1 + 2

