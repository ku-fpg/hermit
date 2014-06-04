{-# LANGUAGE DeriveDataTypeable, TypeFamilies #-}
module HERMIT.Dictionary.WorkerWrapper.Common
    ( WWAssumptionTag(..)
    , WWAssumption(..)
    , assumptionAEqualityT
    , assumptionBEqualityT
    , assumptionCEqualityT
    , workLabel
    ) where

import Data.Typeable

import HERMIT.Core
import HERMIT.External
import HERMIT.GHC
import HERMIT.Kure
import HERMIT.Monad
import HERMIT.ParserCore

import HERMIT.Dictionary.Function
import HERMIT.Dictionary.Reasoning

--------------------------------------------------------------------------------------------------

data WWAssumptionTag = A | B | C deriving (Eq,Ord,Show,Read,Typeable)

instance Extern WWAssumptionTag where
    type Box WWAssumptionTag = WWAssumptionTag
    box i = i
    unbox i = i

data WWAssumption = WWAssumption WWAssumptionTag (RewriteH CoreExpr)

--------------------------------------------------------------------------------------------------

-- Note: The current approach to WW Fusion is a hack.
-- I'm not sure what the best way to approach this is though.
-- An alternative would be to have a generate command that adds ww-fusion to the dictionary, all preconditions verified in advance.
-- That would have to exist at the Shell level though.

-- This isn't entirely safe, as a malicious the user could define a label with this name.
workLabel :: Label
workLabel = "recursive-definition-of-work-for-use-by-ww-fusion"

--------------------------------------------------------------------------------------------------

-- TODO: generalize away from TransformH on all of these

-- Given abs and rep expressions, build "abs . rep = id"
assumptionAEqualityT :: CoreString -> CoreString -> TransformH x CoreExprEquality
assumptionAEqualityT absC repC = prefixFailMsg "Building assumption A failed: " $ do
    absE <- parseCoreExprT absC
    repE <- parseCoreExprT repC
    comp <- buildCompositionT absE repE
    let (_,compBody) = collectTyBinders comp
    (tvs, xTy, _) <- funTyComponentsM (exprType comp)
    idE <- buildIdT xTy
    return $ CoreExprEquality tvs compBody idE

-- Given abs, rep, and f expressions, build "abs . rep . f = f"
assumptionBEqualityT :: CoreString -> CoreString -> CoreString -> TransformH x CoreExprEquality
assumptionBEqualityT absC repC fC = prefixFailMsg "Building assumption B failed: " $ do
    absE <- parseCoreExprT absC
    repE <- parseCoreExprT repC
    fE   <- parseCoreExprT fC
    repAfterF <- buildCompositionT repE fE
    comp <- buildCompositionT absE repAfterF
    let (tvs,lhs) = collectTyBinders comp
    rhs <- appArgM 5 lhs >>= appArgM 5 -- get f with proper tvs applied
    return $ CoreExprEquality tvs lhs rhs

-- Given abs, rep, and f expressions, build "fix (abs . rep . f) = fix f"
assumptionCEqualityT :: CoreString -> CoreString -> CoreString -> TransformH x CoreExprEquality
assumptionCEqualityT absC repC fC = prefixFailMsg "Building assumption C failed: " $ do
    CoreExprEquality vs lhs rhs <- assumptionBEqualityT absC repC fC
    lhs' <- buildFixT lhs
    rhs' <- buildFixT rhs
    return $ CoreExprEquality vs lhs' rhs'
