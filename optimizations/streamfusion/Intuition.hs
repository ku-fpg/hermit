{-# LANGUAGE BangPatterns, RankNTypes #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}
{-# OPTIONS_GHC -fspec-constr #-}
{-# OPTIONS_GHC -fdicts-cheap #-}

module Main where

import Criterion.Main as C

import HERMIT.Optimization.StreamFusion.List

f :: Int -> Int
f n = foldl (+) 0 (concatMap (\x -> enumFromTo 1 x) (enumFromTo 1 n))
{-# NOINLINE f #-}

g :: Int -> Int
g n = foldl (+) 0 (flatten mk step (enumFromTo 1 n))
  where
    mk x = (1,x)
    {-# INLINE mk #-}
    step (i,max)
      | i<=max = Yield i (i+1,max)
      | otherwise = Done
    {-# INLINE step #-}
{-# NOINLINE g #-}

main = do
  print $ f 1000
  print $ g 1000
  defaultMain
    [ bgroup "concat tests / 100"
      [ bench "f" $ whnf f 100
      , bench "g" $ whnf g 100
      ]
    , bgroup "concat tests / 1000"
      [ bench "f" $ whnf f 1000
      , bench "g" $ whnf g 1000
      ]
    ]

