{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RankNTypes #-}

{-# OPTIONS_GHC -funbox-strict-fields #-}
{-# OPTIONS_GHC -fspec-constr #-}
{-# OPTIONS_GHC -fdicts-cheap #-}
{-# OPTIONS_GHC -optlo-O3 -optlc-O3 #-} -- this is fast...

module Main where

import Data.Strict.Tuple
import Data.Vector.Fusion.Stream.Monadic as SM

import HERMIT.Optimization.StreamFusion.Vector

main :: IO ()
main = testDeep >>= print

class Deep x where
  deep :: x -> SM.Stream IO Int

instance Deep Int where
  deep !k = SM.enumFromStepN 1 1 k
  {-# INLINABLE deep #-}

instance Deep x => Deep (x :!: Int) where
  deep !(x :!: k) = SM.concatMap (SM.enumFromStepN 1 1) $ deep x
  {-# INLINABLE deep #-}

testDeep :: IO Int
testDeep = SM.foldl' (+) 0 $ deep (( (10::Int) :!: (12::Int)) :!: (14::Int) :!: (15::Int))
{-# NOINLINE testDeep #-}

