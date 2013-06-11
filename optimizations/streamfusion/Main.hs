module Main where

import Criterion.Main
import HERMIT.Optimization.StreamFusion.List

main = defaultMain [ bgroup "test" [ bench "100" $ whnf test 100
                                   , bench "1000" $ whnf test 1000
--                                   , bench "10000" $ whnf test 10000
                                   ] ]

test n = foldl (+) 0 . filter odd . concatMap (\(m,n) -> [m..n]) . zip [1..n] $ [n..2*n]
