{-# LANGUAGE ScopedTypeVariables #-}

module HERMIT.Dictionary
    ( -- * The HERMIT Dictionary
      externals
    ) where

import HERMIT.External

import qualified HERMIT.Primitive.AlphaConversion as Alpha
import qualified HERMIT.Primitive.Composite as Composite
import qualified HERMIT.Primitive.Debug as Debug
import qualified HERMIT.Primitive.FixPoint as FixPoint
import qualified HERMIT.Primitive.Fold as Fold
import qualified HERMIT.Primitive.Function as Function
import qualified HERMIT.Primitive.GHC as GHC
import qualified HERMIT.Primitive.Inline as Inline
import qualified HERMIT.Primitive.Kure as Kure
import qualified HERMIT.Primitive.Local as Local
import qualified HERMIT.Primitive.Navigation as Navigation
import qualified HERMIT.Primitive.New as New
import qualified HERMIT.Primitive.Query as Query
import qualified HERMIT.Primitive.Reasoning as Reasoning
import qualified HERMIT.Primitive.Undefined as Undefined
import qualified HERMIT.Primitive.Unfold as Unfold
import qualified HERMIT.Primitive.Unsafe as Unsafe
import qualified HERMIT.Primitive.WorkerWrapper.Fix as WorkerWrapperFix
import qualified HERMIT.Primitive.WorkerWrapper.FixResult as WorkerWrapperFixResult

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
