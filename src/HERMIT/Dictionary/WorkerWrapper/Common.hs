{-# LANGUAGE DeriveDataTypeable, TypeFamilies #-}
module HERMIT.Dictionary.WorkerWrapper.Common
    ( externals
    , WWAssumptionTag(..)
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

import HERMIT.Dictionary.Function hiding (externals)
import HERMIT.Dictionary.Reasoning hiding (externals)

--------------------------------------------------------------------------------------------------

-- | New Worker/Wrapper-related externals.
externals :: [External]
externals = map (.+ Proof)
    [ external "intro-ww-assumption-A"
               (\nm absC repC -> assumptionAEqualityT absC repC >>= insertLemmaR nm :: RewriteH Core)
               [ "Introduce a lemma for worker/wrapper assumption A"
               , "using given abs and rep functions." ]
    , external "intro-ww-assumption-B"
               (\nm absC repC bodyC -> assumptionBEqualityT absC repC bodyC >>= insertLemmaR nm :: RewriteH Core)
               [ "Introduce a lemma for worker/wrapper assumption B"
               , "using given abs, rep, and body functions." ]
    , external "intro-ww-assumption-C"
               (\nm absC repC bodyC -> assumptionCEqualityT absC repC bodyC >>= insertLemmaR nm :: RewriteH Core)
               [ "Introduce a lemma for worker/wrapper assumption C"
               , "using given abs, rep, and body functions." ]
    ]

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
assumptionAEqualityT :: CoreString -> CoreString -> TransformH x Equality
assumptionAEqualityT absC repC = prefixFailMsg "Building assumption A failed: " $ do
    absE <- parseCoreExprT absC
    repE <- parseCoreExprT repC
    comp <- buildCompositionT absE repE
    let (_,compBody) = collectTyBinders comp
    (tvs, xTy, _) <- funTyComponentsM (exprType comp)
    idE <- buildIdT xTy
    return $ Equality tvs compBody idE

-- Given abs, rep, and f expressions, build "abs . rep . f = f"
assumptionBEqualityT :: CoreString -> CoreString -> CoreString -> TransformH x Equality
assumptionBEqualityT absC repC fC = prefixFailMsg "Building assumption B failed: " $ do
    absE <- parseCoreExprT absC
    repE <- parseCoreExprT repC
    fE   <- parseCoreExprT fC
    repAfterF <- buildCompositionT repE fE
    comp <- buildCompositionT absE repAfterF
    let (tvs,lhs) = collectTyBinders comp
    rhs <- appArgM 5 lhs >>= appArgM 5 -- get f with proper tvs applied
    return $ Equality tvs lhs rhs

-- Given abs, rep, and f expressions, build "fix (abs . rep . f) = fix f"
assumptionCEqualityT :: CoreString -> CoreString -> CoreString -> TransformH x Equality
assumptionCEqualityT absC repC fC = prefixFailMsg "Building assumption C failed: " $ do
    Equality vs lhs rhs <- assumptionBEqualityT absC repC fC
    lhs' <- buildFixT lhs
    rhs' <- buildFixT rhs
    return $ Equality vs lhs' rhs'
