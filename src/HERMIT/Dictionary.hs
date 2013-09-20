{-# LANGUAGE ScopedTypeVariables #-}

module HERMIT.Dictionary
    ( -- * The HERMIT Dictionary
      externals
    ) where

import HERMIT.External

import qualified HERMIT.Dictionary.AlphaConversion as Alpha
import qualified HERMIT.Dictionary.Composite as Composite
import qualified HERMIT.Dictionary.Debug as Debug
import qualified HERMIT.Dictionary.FixPoint as FixPoint
import qualified HERMIT.Dictionary.Fold as Fold
import qualified HERMIT.Dictionary.Function as Function
import qualified HERMIT.Dictionary.GHC as GHC
import qualified HERMIT.Dictionary.Inline as Inline
import qualified HERMIT.Dictionary.Kure as Kure
import qualified HERMIT.Dictionary.Local as Local
import qualified HERMIT.Dictionary.Navigation as Navigation
import qualified HERMIT.Dictionary.New as New
import qualified HERMIT.Dictionary.Query as Query
import qualified HERMIT.Dictionary.Reasoning as Reasoning
import qualified HERMIT.Dictionary.Undefined as Undefined
import qualified HERMIT.Dictionary.Unfold as Unfold
import qualified HERMIT.Dictionary.Unsafe as Unsafe
import qualified HERMIT.Dictionary.WorkerWrapper.Fix as WorkerWrapperFix
import qualified HERMIT.Dictionary.WorkerWrapper.FixResult as WorkerWrapperFixResult

--------------------------------------------------------------------------

-- | List of all 'External's provided by HERMIT.
externals :: [External]
externals =
       Alpha.externals
    ++ Composite.externals
    ++ Debug.externals
    ++ FixPoint.externals
    ++ Fold.externals
    ++ Function.externals
    ++ GHC.externals
    ++ Inline.externals
    ++ Kure.externals
    ++ Local.externals
    ++ Navigation.externals
    ++ New.externals
    ++ Query.externals
    ++ Reasoning.externals
    ++ Undefined.externals
    ++ Unfold.externals
    ++ Unsafe.externals
    ++ WorkerWrapperFix.externals
    ++ WorkerWrapperFixResult.externals
