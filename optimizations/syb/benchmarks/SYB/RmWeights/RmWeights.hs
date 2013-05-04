module SYB.RmWeights.RmWeights where

import Data.Generics
import TreeDatatype(WTree(WithWeight))
-- import TreeReps

rmWeights :: Data a => a -> a
rmWeights = everywhere (mkT rmAdhoc)
  where
  -- It is a pity that an ad-hoc case for a type
  -- constructor is not easy to do in SYB
  -- (no mkT2!!)
  rmAdhoc :: WTree Int Int -> WTree Int Int
  rmAdhoc (WithWeight t w) = t -- Constructor ad-hoc case
  rmAdhoc t                = t -- Generic case (no need to handle, everywhere takes care of it)
