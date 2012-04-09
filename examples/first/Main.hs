{-# LANGUAGE TemplateHaskell #-}
-- This is a first example of using Hermit.
-- To run use,
-- % ghc-7.4.1 -fplugin=Language.HERMIT.Plugin Main.hs -fplugin-opt=Language.HERMIT.Plugin:cl -fforce-recomp

module Main where

import Language.HERMIT

main = print (fib 45)

fib :: Int -> Int
fib n = if n < 2 then 1 else fib(n-1) + fib (n-2)

