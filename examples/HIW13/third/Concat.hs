{-# LANGUAGE BangPatterns, RankNTypes #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}
{-# OPTIONS_GHC -fspec-constr #-}
{-# OPTIONS_GHC -fdicts-cheap #-}

{-# OPTIONS_GHC -optlo-O3 -optlc-O3 #-} -- this is fast...

module Main where

import Data.Vector.Fusion.Stream as VS
import Data.Vector.Fusion.Stream.Monadic as M
import Data.Vector.Fusion.Stream.Size as VS

import HERMIT.Optimization.StreamFusion.Vector

concatTestS :: Int -> Int
concatTestS n = VS.foldl' (+) 0 $ VS.concatMap (\(!x) -> VS.enumFromStepN 1 1 x) $ VS.enumFromStepN 1 1 n
{-# NOINLINE concatTestS #-}

flattenTest :: Int -> Int
flattenTest !n = VS.foldl' (+) 0 $ VS.flatten mk step Unknown $ VS.enumFromStepN 1 1 n
  where
    mk !x = (1,x)
    {-# INLINE mk #-}
    step (!i,!max)
--      | i<=max = VS.Yield i (i+1,max)
      | max>(0::Int) = VS.Yield i (i+1,max-1) -- 10% faster
      | otherwise = VS.Done
    {-# INLINE step #-}
{-# NOINLINE flattenTest #-}

main :: IO ()
main = do
  print $ concatTestS 20000
  print $ flattenTest 20000
