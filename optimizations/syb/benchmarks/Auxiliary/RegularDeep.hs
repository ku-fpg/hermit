{-# LANGUAGE EmptyDataDecls        #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}

module Auxiliary.RegularDeep where

import Auxiliary.Tree (Tree(..))
import RegularDeep.Functions


-- Regular instances
data Bin
instance Constructor Bin  where conName _ = "Bin"
data Leaf
instance Constructor Leaf where conName _ = "Leaf"

type instance PF (Tree a) =       C Bin  (K a :*: I :*: I)
                              :+: C Leaf U

instance Regular (Tree a) where
  from (Bin x l r) = In (L (C (K x :*: I (from l) :*: I (from r))))
  from Leaf        = In (R (C U))

  to (In (L (C (K x :*: (I l) :*: (I r))))) = Bin x (to l) (to r)
  to (In (R (C U)))                         = Leaf
