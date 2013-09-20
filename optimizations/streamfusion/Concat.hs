{-# LANGUAGE BangPatterns, RankNTypes #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}
{-# OPTIONS_GHC -fspec-constr #-}
{-# OPTIONS_GHC -fdicts-cheap #-}

{- OPTIONS_GHC -optlo-globalopt #-}
{- OPTIONS_GHC -optlo-loop-unswitch #-}
{- OPTIONS_GHC -optlo-mem2reg #-}
{- OPTIONS_GHC -optlo-prune-eh #-}

{-# OPTIONS_GHC -optlo-O3 -optlc-O3 #-} -- this is fast...

module Main where

import Data.Vector as V
import GHC.Enum as E
import Data.Vector.Fusion.Stream as VS
import Data.Vector.Fusion.Stream.Monadic as M
import Data.Vector.Fusion.Stream.Size as VS

import Criterion.Main as C
import Control.Monad.ST
import qualified Data.Vector.Unboxed.Mutable as VUM
import qualified Data.Vector.Unboxed as VU

import HERMIT.Optimization.StreamFusion.Vector

-- | Note: Data.Vector.concatMap = Data.Vector.Generic.concatMap
--         which is implemented in terms of flatten (with entire
--         inner vector in state, so not properly fused).
--         We cannot hope to optimize this.
concatTestV :: Int -> Int
concatTestV n = V.sum $ V.concatMap (\(!x) -> V.enumFromN 1 x) $ V.enumFromN 1 n
{-# NOINLINE concatTestV #-}

concatTestS :: Int -> Int
concatTestS n = VS.foldl' (+) 0 $ VS.concatMap (\(!x) -> VS.enumFromStepN 1 1 x) $ VS.enumFromStepN 1 1 n
{-# NOINLINE concatTestS #-}

-- | And again, this time we flatten the resulting stream. If this is fast
-- (enough), we can start the fusion process on ADP.
--
-- NOTE This does actually reduce to the desired tight loop.

flattenTest :: Int -> Int
flattenTest !n = VS.foldl' (+) 0 $ VS.flatten mk step Unknown $ VS.enumFromStepN 1 1 n
  where
    mk !x = (1,x)
    {-# INLINE mk #-}
    step (!i,!max)
      | i<=max = VS.Yield i (i+1,max)
--      | max>(0::Int) = VS.Yield i (i+1,max-1) -- 10% faster
      | otherwise = VS.Done
    {-# INLINE step #-}
{-# NOINLINE flattenTest #-}

flattenTestDown :: Int -> Int
flattenTestDown !n = VS.foldl' (+) 0 $ VS.flatten mk step Unknown $ VS.enumFromStepN 1 1 n
  where
    mk !x = (x,1)
    {-# INLINE mk #-}
    step (!i,!min)
      | i>=min = VS.Yield i (i-1,min)
      | otherwise = VS.Done
    {-# INLINE step #-}
{-# NOINLINE flattenTestDown #-}

-- nestedConcatS 3 = sum [1,1,2,2,1,2,3,2,3,3]
nestedConcatS :: Int -> Int
nestedConcatS n = VS.foldl' (+) 0 $ VS.concatMap (\(!x) -> VS.concatMap (\(!y) -> VS.enumFromStepN y 1 x) $ VS.enumFromStepN 1 1 x) $ VS.enumFromStepN 1 1 n
{-# NOINLINE nestedConcatS #-}

concatMapMonadic :: Int -> Int
concatMapMonadic k = runST $ do
    tbl <- VU.thaw $ VU.fromList [0 .. k]
    M.foldl' (+) 0 $ M.concatMapM (\(!x) -> VUM.unsafeRead tbl x >>= \z -> return $ M.enumFromStepN 1 1 z) $ M.enumFromStepN 1 1 k
{-# NOINLINE concatMapMonadic #-}

{-
nestedFlatten :: Int -> Int
nestedFlatten !n = VS.foldl' (+) 0 $ VS.flatten mk step Unknown $ VS.enumFromStepN 1 1 n
  where
    mk !x = (1,1,x)
    {-# INLINE mk #-}
    step (!i,!j,!x)
      | (i<=x) && (j<=i) = VS.Yield j (i,j+1,x)
      |  i<=x            = VS.Skip (i+1,1,x)
      | otherwise          = VS.Done
    {-# INLINE step #-}
{-# NOINLINE nestedFlatten #-}
-}

main = do
--  print $ concatTestV 1000
  print $ concatTestS 1000
  print $ flattenTest 1000
  print $ concatMapMonadic 1000
--  print $ flattenTestDown 1000
  putStrLn $ "nestedConcatS: " Prelude.++ (show $ nestedConcatS 100)
--  putStrLn $ "nestedFlatten: " Prelude.++ (show $ nestedFlatten 100)
  defaultMain
    [ bgroup "concat tests / 100"
      [ bench "concatTestS" $ whnf concatTestS 100
--      , bench "concatTestV" $ whnf concatTestV 100
      , bench "flattenTest" $ whnf flattenTest 100
      , bench "concatMapMonadic" $ whnf concatMapMonadic 100
      ]
    , bgroup "concat tests / 1000"
      [ bench "concatTestS" $ whnf concatTestS 1000
--      , bench "concatTestV" $ whnf concatTestV 1000
      , bench "flattenTest" $ whnf flattenTest 1000
      , bench "concatMapMonadic" $ whnf concatMapMonadic 1000
      ]
{- for paper
    , bgroup "concat tests / 5000"
      [ bench "concatTestS" $ whnf concatTestS 5000
      , bench "flattenTest" $ whnf flattenTest 5000
      ]
    , bgroup "concat tests / 10000"
      [ bench "concatTestS" $ whnf concatTestS 10000
      , bench "flattenTest" $ whnf flattenTest 10000
      ]
    , bgroup "concat tests / 20000"
      [ bench "concatTestS" $ whnf concatTestS 20000
      , bench "flattenTest" $ whnf flattenTest 20000
      ]
-}
    , bgroup "nested tests / 100"
      [ bench "nestedConcatS" $ whnf nestedConcatS 100
      ]
{-
    , bgroup "nested tests / 10"
      [ bench "nestedConcatS" $ whnf nestedConcatS 10
      , bench "nestedFlatten" $ whnf nestedFlatten 10
      ]
    , bgroup "nested tests / 100"
      [ bench "nestedConcatS" $ whnf nestedConcatS 100
      , bench "nestedFlatten" $ whnf nestedFlatten 100
      ]
-}
    ]

