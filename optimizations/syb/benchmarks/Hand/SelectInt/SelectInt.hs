module Hand.SelectInt.SelectInt where

import TreeDatatype

selectInt :: WTree Int Int -> [Int]
selectInt = loop []
  where
    loop acc (Leaf x) = x : acc
    loop acc (Fork l r) = loop (loop acc r) l
    loop acc (WithWeight t w) = loop (w : acc) t
