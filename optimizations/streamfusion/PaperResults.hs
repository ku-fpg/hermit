{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE BangPatterns #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}
{-# OPTIONS_GHC -fspec-constr #-}
{-# OPTIONS_GHC -fdicts-cheap #-}
{-# OPTIONS_GHC -optlo-O3 -optlc-O3 #-} -- this is fast...


module Main where

import Data.Vector as V
import GHC.Enum as E
import Data.Vector.Fusion.Stream as VS
import Data.Vector.Fusion.Stream.Monadic as M
import Data.Vector.Fusion.Stream.Size as VS
import qualified Data.List as L

import Criterion.Main as C
import Control.Monad.ST
import qualified Data.Vector.Unboxed.Mutable as VUM
import qualified Data.Vector.Unboxed as VU
import Control.Monad.Primitive
import Data.Monoid

import HERMIT.Optimization.StreamFusion.Vector
--import HERMIT.Optimization.StreamFusion


-- concatMap / enumStepFromN

listCmEfs :: Int -> Int
listCmEfs n = L.foldl' (+) 0 $ L.concatMap (\x -> [1..x]) [1..n]
{-# NOINLINE listCmEfs #-}

vectorCmEfs :: Int -> Int
vectorCmEfs n = VS.foldl' (+) 0 $ VS.concatMap (\(!x) -> VS.enumFromStepN 1 1 x) $ VS.enumFromStepN 1 1 n
{-# NOINLINE vectorCmEfs #-}

flattenCmEfs :: Int -> Int
flattenCmEfs n = VS.foldl' (+) 0 $ VS.flatten mk step Unknown $ VS.enumFromStepN 1 1 n where
  mk x = (x,1)
  step (x,k)
    | k>x = VS.Done
    | otherwise = VS.Yield k (x,k+1)
{-# NOINLINE flattenCmEfs #-}

-- concatMap / concatMap

listCmCm :: Int -> Int
listCmCm n = L.foldl' (+) 0 $ L.concatMap (\x -> L.concatMap (\y -> [y..x]) [1..x]) [1..n]
{-# NOINLINE listCmCm #-}

vectorCmCm :: Int -> Int
vectorCmCm n = VS.foldl' (+) 0
             $ VS.concatMap (\x -> VS.concatMap (\y -> VS.enumFromStepN y 1 (x-y+1)) $
                                                VS.enumFromStepN 1 1 x)
             $ VS.enumFromStepN 1 1 n
{-# NOINLINE vectorCmCm #-}

flattenCmCm :: Int -> Int
flattenCmCm n = VS.foldl' (+) 0 $ VS.flatten mk step Unknown $ VS.enumFromStepN 1 1 n where
  mk x = (x,1,1)
  step (x,y,k)
    | y>x = VS.Done
    | k>x = VS.Skip (x,y+1,y+1)
    | otherwise = VS.Yield k (x,y,k+1)
{-# NOINLINE flattenCmCm #-}


-- concatMap monadic

staticV = VU.fromList [ 0 .. 10000 :: Int]
{-# NOINLINE staticV #-}

vector_cmm :: Int -> Int
vector_cmm k = runST $ do
    tbl <- VU.unsafeThaw staticV
    M.foldl' (+) 0 $ M.concatMapM (\(!x) -> VUM.unsafeRead tbl x >>=
                        \z -> return $ M.mapM (\(!y) -> VUM.unsafeRead tbl y) $ M.enumFromStepN 1 1 z)
      $ M.enumFromStepN 1 1 k
{-# NOINLINE vector_cmm #-}

flatten_cmm :: Int -> Int
flatten_cmm k = runST $ do
  tbl <- VU.unsafeThaw staticV
  let mk x = VUM.unsafeRead tbl x >>= \z -> return (x,z,1)
  let step (x,z,k) = do y <- VUM.unsafeRead tbl k
                        if | z>x -> return $ M.Done
                           | k>z -> return $ M.Skip (x,z+1,1)
                           | otherwise -> return $ M.Yield k (x,z,k+1)
  M.foldl' (+) 0 $ M.flatten mk step Unknown $ M.enumFromStepN 1 1 k
{-# NOINLINE flatten_cmm #-}

-- choice

list_choice :: Int -> Int
list_choice n = L.foldl' (+) 0 $ L.concatMap (\x -> if odd x then [1..x] else [2..x]) [1..n]
{-# NOINLINE list_choice #-}

vector_choice :: Int -> Int
vector_choice n = VS.foldl' (+) 0
                $ VS.concatMap (\x -> if odd x then VS.enumFromStepN 1 1 x else VS.enumFromStepN 2 1 (x-1))
                $ VS.enumFromStepN 1 1 n
{-# NOINLINE vector_choice #-}

flatten_choice :: Int -> Int
flatten_choice n = VS.foldl' (+) 0 $ VS.flatten mk step Unknown $ VS.enumFromStepN 1 1 n where
  mk x = (x,if odd x then 1 else 2)
  step (x,k)
    | k>x = VS.Done
    | otherwise = VS.Yield k (x,k+1)
{-# NOINLINE flatten_choice #-}

-- monoid
--list_monoid :: Int -> Maybe Int
--list_monoid n = L.foldl' mappend mempty

main = do
  print $ listCmEfs 100 == vectorCmEfs 100
  print $ listCmCm  100 == vectorCmCm  100
  print $ vector_cmm 100 == flatten_cmm 100
  print $ list_choice 100 == vector_choice 100
  defaultMain
    [ bgroup "enum"
      [ bench "listCmEfs" $ whnf listCmEfs 1000
      , bench "vectorCmEfs" $ whnf vectorCmEfs 1000
      , bench "flattenCmEfs" $ whnf flattenCmEfs 1000
      ]
    , bgroup "nested"
      [ bench "listCmCm" $ whnf listCmCm 200
      , bench "vectorCmCm" $ whnf vectorCmCm 200
      , bench "flattenCmCm" $ whnf flattenCmCm 200
      ]
    , bgroup "monadic"
      [ bench "vector_cmm" $ whnf vector_cmm 1000
      , bench "flatten_cmm" $ whnf flatten_cmm 1000
      ]
    , bgroup "choice"
      [ bench "list_choice" $ whnf list_choice 1000
      , bench "vector_choice" $ whnf vector_choice 1000
      , bench "flatten_choice" $ whnf flatten_choice 1000
      ]
{-
    , bgroup "5000"
      [ bench "listCmEfs" $ whnf listCmEfs 5000
      , bench "vectorCmEfs" $ whnf vectorCmEfs 5000
      , bench "flattenCmEfs" $ whnf flattenCmEfs 5000
      --
      , bench "listCmCm" $ whnf listCmCm 5000
      , bench "vectorCmCm" $ whnf vectorCmCm 5000
      , bench "flattenCmCm" $ whnf flattenCmCm 5000
      --
      , bench "vector_cmm" $ whnf vector_cmm 5000
      , bench "flatten_cmm" $ whnf flatten_cmm 5000
      , bench "flatten_cmm" $ whnf flatten_cmm 5000
      --
      , bench "list_choice" $ whnf list_choice 5000
      , bench "vector_choice" $ whnf vector_choice 5000
      , bench "flatten_choice" $ whnf flatten_choice 5000
      ]
-}
    ]

