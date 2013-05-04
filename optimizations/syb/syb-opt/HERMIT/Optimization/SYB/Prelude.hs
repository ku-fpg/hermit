{-# LANGUAGE CPP #-}
module HERMIT.Optimization.SYB.Prelude
    ( -- re-export all the imports below, so inlining info is available
      -- during compilation of the target program
      module Data.Function
    , module GHC.Base
    , module GHC.Fingerprint
    , module GHC.Fingerprint.Type
    , module GHC.Prim
    , module GHC.Word
    ) where

import Data.Function (fix)
import GHC.Base((++))
import GHC.Fingerprint (fingerprintFingerprints, Fingerprint(..))
import GHC.Fingerprint.Type
import GHC.Prim -- eqWord#
import GHC.Word

-- After 7.6, GHC supports rules that never fire automatically.
#if __GLASGOW_HASKELL__ > 706
{-# RULES "[]++"   [~] forall x. [] ++ x = x      #-}
{-# RULES "append" [~]           (++)    = append #-}
#else
{-# RULES "[]++"   forall x. [] ++ x = x #-}
{-# RULES "append"           (++)    = append #-}
#endif

append :: [a] -> [a] -> [a]
append []     xs = xs
append (y:ys) xs = y : append ys xs
