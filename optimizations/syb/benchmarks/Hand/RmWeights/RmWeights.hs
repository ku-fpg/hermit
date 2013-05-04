module Hand.RmWeights.RmWeights where

import TreeDatatype

rmWeights :: WTree Int Int -> WTree Int Int
rmWeights (WithWeight t w) = rmWeights t
rmWeights (Leaf x)         = Leaf x
rmWeights (Fork l r)       = Fork (rmWeights l) (rmWeights r)
