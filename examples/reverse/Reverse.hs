module Reverse where

import Prelude hiding (reverse)

main = print $ last $ reverse [1..15000 :: Int]

reverse []     = []
reverse (x:xs) = reverse xs ++ [x]
