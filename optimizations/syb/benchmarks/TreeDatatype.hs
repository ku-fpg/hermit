{-# LANGUAGE DeriveDataTypeable #-}
module TreeDatatype where

import Data.Generics

-- A parameterised datatype for binary trees with data at the leafs
--   and possible "weight" labels
data WTree a w = Leaf a
               | Fork (WTree a w) (WTree a w)
               | WithWeight (WTree a w) w
       deriving (Show, Typeable, Data, Eq)

-- A typical tree
mytree :: WTree Int Int
mytree = Fork (WithWeight (Leaf 42) 1)
              (WithWeight (Fork (Leaf 88) (Leaf 37)) 2)

-- and another
mytree2 :: WTree Int Int
mytree2 = Fork (Leaf 42)
               (WithWeight (Fork (Leaf 88) (Leaf 37)) 3)

-- yet one more
mytree3 :: WTree Int Int
mytree3 = Fork (WithWeight (Leaf 42) 1)
               (WithWeight (Leaf 88) 2)

-- this one has nested weights
mytree4 :: WTree Int Int
mytree4 = Fork (WithWeight (WithWeight (Leaf 42) 1) 1)
               (WithWeight (Leaf 88) 2)


-- Constructors for larger WTrees

mkWTree :: Int -> WTree Int Int
mkWTree n | n <= 1 = Leaf n
          | even n = WithWeight (mkWTree (div n 2)) n
          | otherwise = Fork (mkWTree (3*n+1)) (mkWTree (n-1))

mkFullWTree :: Int -> WTree Int Int
mkFullWTree d | d <= 1 = Leaf d
              | even d = WithWeight (mkFullWTree $ d-3) d
              | otherwise = Fork (mkFullWTree $ d-1) (mkFullWTree $ d+1)

powerOfTwo :: Int -> WTree a w -> WTree a w
powerOfTwo 0 t = t
powerOfTwo n t = Fork (powerOfTwo (n-1) t) (powerOfTwo (n-1) t)

onewtree = mkWTree 15
bigwtree n = powerOfTwo n onewtree

sizeWTree = go 0
    where -- go s _ | s > 500000   = 500000
          go s (Leaf _)         = s + 1
          go s (Fork l r)       = go (1 + go s l) r
          go s (WithWeight t w) = go (s+1) t

sumWTree :: WTree Int Int -> Int
sumWTree = go 0
    where go s (Leaf i) = s + i
          go s (Fork l r) = go (go s l) r
          go s (WithWeight t w) = go (s + w) t

deepSeqWTree (Leaf x)         = seq x
deepSeqWTree (Fork l r)       = deepSeqWTree l . deepSeqWTree r
deepSeqWTree (WithWeight t w) = deepSeqWTree t . seq w
