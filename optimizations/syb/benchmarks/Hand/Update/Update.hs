module Hand.Update.Update where

import Auxiliary.Tree (Tree(..))
import Auxiliary.Logic (Logic(..))

updateTree :: Tree Int -> Tree Int
updateTree Leaf        = Leaf
updateTree (Bin n l r) | odd n     = (Bin (n+1)) (updateTree l) (updateTree r)
                       | otherwise = (Bin (n-1)) (updateTree l) (updateTree r)

updateLogic :: (Char -> Char) -> Logic -> Logic
updateLogic f l = go l
  where
    go (Var s i)   = Var (map f s) i
    go (Impl  p q) = Impl  (go p) (go q)
    go (Equiv p q) = Equiv (go p) (go q)
    go (Conj  p q) = Conj  (go p) (go q)
    go (Disj  p q) = Disj  (go p) (go q)
    go (Not p)     = Not (go p)
    go T           = T
    go F           = F
