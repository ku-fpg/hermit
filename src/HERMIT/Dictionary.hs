module HERMIT.Dictionary
    ( -- * The HERMIT Dictionary
      externals
    , module HERMIT.Dictionary.AlphaConversion
    , module HERMIT.Dictionary.Common
    , module HERMIT.Dictionary.Composite
    , module HERMIT.Dictionary.Debug
    , module HERMIT.Dictionary.FixPoint
    , module HERMIT.Dictionary.Fold
    , module HERMIT.Dictionary.Function
    , module HERMIT.Dictionary.GHC
    , module HERMIT.Dictionary.Inline
    , module HERMIT.Dictionary.Kure
    , module HERMIT.Dictionary.Local
    , module HERMIT.Dictionary.Navigation
    , module HERMIT.Dictionary.New
    , module HERMIT.Dictionary.Query
    , module HERMIT.Dictionary.Reasoning
    , module HERMIT.Dictionary.Rules
    , module HERMIT.Dictionary.Undefined
    , module HERMIT.Dictionary.Unfold
    , module HERMIT.Dictionary.Unsafe
    , module HERMIT.Dictionary.WorkerWrapper.Common -- TODO: rename
    , module HERMIT.Dictionary.WorkerWrapper.Fix
    , module HERMIT.Dictionary.WorkerWrapper.FixResult
    ) where

import HERMIT.External

-- Since you cannot re-export qualified modules, we import everything *twice*.
import           HERMIT.Dictionary.AlphaConversion hiding (externals)
import qualified HERMIT.Dictionary.AlphaConversion as Alpha
import           HERMIT.Dictionary.Common -- TODO: deal with this module
import           HERMIT.Dictionary.Composite hiding (externals)
import qualified HERMIT.Dictionary.Composite as Composite
import           HERMIT.Dictionary.Debug hiding (externals)
import qualified HERMIT.Dictionary.Debug as Debug
import           HERMIT.Dictionary.FixPoint hiding (externals)
import qualified HERMIT.Dictionary.FixPoint as FixPoint
import           HERMIT.Dictionary.Fold hiding (externals)
import qualified HERMIT.Dictionary.Fold as Fold
import           HERMIT.Dictionary.Function hiding (externals)
import qualified HERMIT.Dictionary.Function as Function
import           HERMIT.Dictionary.GHC hiding (externals)
import qualified HERMIT.Dictionary.GHC as GHC
import           HERMIT.Dictionary.Inline hiding (externals)
import qualified HERMIT.Dictionary.Inline as Inline
import           HERMIT.Dictionary.Kure hiding (externals)
import qualified HERMIT.Dictionary.Kure as Kure
import           HERMIT.Dictionary.Local hiding (externals)
import qualified HERMIT.Dictionary.Local as Local
import           HERMIT.Dictionary.Navigation hiding (externals)
import qualified HERMIT.Dictionary.Navigation as Navigation
import           HERMIT.Dictionary.New hiding (externals)
import qualified HERMIT.Dictionary.New as New
import           HERMIT.Dictionary.Query hiding (externals)
import qualified HERMIT.Dictionary.Query as Query
import           HERMIT.Dictionary.Reasoning hiding (externals)
import qualified HERMIT.Dictionary.Reasoning as Reasoning
import           HERMIT.Dictionary.Rules hiding (externals)
import qualified HERMIT.Dictionary.Rules as Rules
import           HERMIT.Dictionary.Undefined hiding (externals)
import qualified HERMIT.Dictionary.Undefined as Undefined
import           HERMIT.Dictionary.Unfold hiding (externals)
import qualified HERMIT.Dictionary.Unfold as Unfold
import           HERMIT.Dictionary.Unsafe hiding (externals)
import qualified HERMIT.Dictionary.Unsafe as Unsafe
import           HERMIT.Dictionary.WorkerWrapper.Common hiding (externals)
import qualified HERMIT.Dictionary.WorkerWrapper.Common as WorkerWrapperCommon
import           HERMIT.Dictionary.WorkerWrapper.Fix hiding (externals)
import qualified HERMIT.Dictionary.WorkerWrapper.Fix as WorkerWrapperFix
import           HERMIT.Dictionary.WorkerWrapper.FixResult hiding (externals)
import qualified HERMIT.Dictionary.WorkerWrapper.FixResult as WorkerWrapperFixResult
--------------------------------------------------------------------------

import qualified HERMIT.PrettyPrinter.AST as AST
import qualified HERMIT.PrettyPrinter.Clean as Clean
import qualified HERMIT.PrettyPrinter.GHC as GHCPP

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
    ++ Rules.externals
    ++ Undefined.externals
    ++ Unfold.externals
    ++ Unsafe.externals
    ++ WorkerWrapperCommon.externals
    ++ WorkerWrapperFix.externals
    ++ WorkerWrapperFixResult.externals
    ++ AST.externals
    ++ Clean.externals
    ++ GHCPP.externals

--------------------------------------------------------------------------
