{-# LANGUAGE TemplateHaskell #-}
-- This is a first example of using Hermit.
-- To run use,
-- % ghc-7.4.1 -fplugin=Language.HERMIT.Plugin Main.hs -fplugin-opt=Language.HERMIT.Plugin:cl -fforce-recomp

module Main where

import Criterion.Main

fib :: Int -> Int
fib n = if n < 2 then 1 else fib(n-1) + fib(n-2)

fib1 :: Int -> Int
fib1 n = if n < 2 then 1 else fib1(n-1) + fib1(n-2)

fib2 :: Int -> Int
fib2 n = if n < 2 then 1 else fib2(n-1) + fib2(n-2)

main = defaultMain
        [ bgroup "original fib"
                     [ bench "35" $ whnf fib 35
                     ]
        , bgroup "unrolled once fib"
                     [ bench "35" $ whnf fib1 35
                     ]
        , bgroup "unrolled twice fib"
                     [ bench "35" $ whnf fib2 35
                     ]
        ]
