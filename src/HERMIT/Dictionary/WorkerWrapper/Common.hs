{-# LANGUAGE CPP, DeriveDataTypeable, TypeFamilies #-}
module HERMIT.Dictionary.WorkerWrapper.Common
    ( externals
    , WWAssumptionTag(..)
    , WWAssumption(..)
    , assumptionAQuantifiedT
    , assumptionBQuantifiedT
    , assumptionCQuantifiedT
    , split1BetaR
    , split2BetaR
    , workLabel
    ) where

import Control.Monad.IO.Class

import Data.String (fromString)
import Data.Typeable

import HERMIT.Context
import HERMIT.Core
import HERMIT.External
import HERMIT.GHC
import HERMIT.Kure
import HERMIT.Lemma
import HERMIT.Monad
import HERMIT.ParserCore

import HERMIT.Dictionary.Common
import HERMIT.Dictionary.Function hiding (externals)
import HERMIT.Dictionary.Reasoning hiding (externals)
import HERMIT.Name

--------------------------------------------------------------------------------------------------

-- | New Worker/Wrapper-related externals.
externals :: [External]
externals = map (.+ Proof)
    [ external "intro-ww-assumption-A"
        (\nm absC repC -> do
            q <- parse2BeforeT assumptionAQuantifiedT absC repC
            insertLemmaT nm $ Lemma q False False :: TransformH Core ())
        [ "Introduce a lemma for worker/wrapper assumption A"
        , "using given abs and rep functions." ]
    , external "intro-ww-assumption-B"
        (\nm absC repC bodyC -> do
            q <- parse3BeforeT assumptionBQuantifiedT absC repC bodyC
            insertLemmaT nm $ Lemma q False False :: TransformH Core ())
        [ "Introduce a lemma for worker/wrapper assumption B"
        , "using given abs, rep, and body functions." ]
    , external "intro-ww-assumption-C"
        (\nm absC repC bodyC -> do
            q <- parse3BeforeT assumptionCQuantifiedT absC repC bodyC
            insertLemmaT nm $ Lemma q False False :: TransformH Core ())
        [ "Introduce a lemma for worker/wrapper assumption C"
        , "using given abs, rep, and body functions." ]
    , external "split-1-beta" (\ nm absC -> promoteExprR . parse2BeforeT (split1BetaR nm) absC :: CoreString -> RewriteH Core)
        [ "split-1-beta <name> <abs expression> <rep expression>"
        , "Perform worker/wrapper split with condition 1-beta."
        , "Given lemma name argument is used as prefix to two introduced lemmas."
        , "  <name>-assumption: unproven lemma for w/w assumption C."
        , "  <name>-fusion: assumed lemma for w/w fusion."
        ]
    , external "split-2-beta" (\ nm absC -> promoteExprR . parse2BeforeT (split2BetaR nm) absC :: CoreString -> RewriteH Core)
        [ "split-2-beta <name> <abs expression> <rep expression>"
        , "Perform worker/wrapper split with condition 2-beta."
        , "Given lemma name argument is used as prefix to two introduced lemmas."
        , "  <name>-assumption: unproven lemma for w/w assumption C."
        , "  <name>-fusion: assumed lemma for w/w fusion."
        ]
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
workLabel :: LemmaName
workLabel = fromString "recursive-definition-of-work-for-use-by-ww-fusion"

--------------------------------------------------------------------------------------------------

-- Given abs and rep expressions, build "abs . rep = id"
assumptionAQuantifiedT :: ( BoundVars c, HasHermitMEnv m, HasHscEnv m
                        , MonadCatch m, MonadIO m, MonadThings m )
                     => CoreExpr -> CoreExpr -> Transform c m x Quantified
assumptionAQuantifiedT absE repE = prefixFailMsg "Building assumption A failed: " $ do
    comp <- buildCompositionT absE repE
    let (_,compBody) = collectTyBinders comp
    (tvs, xTy, _) <- splitFunTypeM (exprType comp)
    idE <- buildIdT xTy
    return $ Quantified tvs (Equiv compBody idE)

-- Given abs, rep, and f expressions, build "abs . rep . f = f"
assumptionBQuantifiedT :: ( BoundVars c, HasHermitMEnv m, HasHscEnv m
                        , MonadCatch m, MonadIO m, MonadThings m)
                     => CoreExpr -> CoreExpr -> CoreExpr -> Transform c m x Quantified
assumptionBQuantifiedT absE repE fE = prefixFailMsg "Building assumption B failed: " $ do
    repAfterF <- buildCompositionT repE fE
    comp <- buildCompositionT absE repAfterF
    let (tvs,lhs) = collectTyBinders comp
    rhs <- appArgM 5 lhs >>= appArgM 5 -- get f with proper tvs applied
    return $ Quantified tvs (Equiv lhs rhs)

-- Given abs, rep, and f expressions, build "fix (abs . rep . f) = fix f"
assumptionCQuantifiedT :: (BoundVars c, HasHermitMEnv m, HasHscEnv m, MonadCatch m, MonadIO m, MonadThings m)
                     => CoreExpr -> CoreExpr -> CoreExpr -> Transform c m x Quantified
assumptionCQuantifiedT absE repE fE = prefixFailMsg "Building assumption C failed: " $ do
    Quantified vs (Equiv lhs rhs) <- assumptionBQuantifiedT absE repE fE
    lhs' <- buildFixT lhs
    rhs' <- buildFixT rhs
    return $ Quantified vs (Equiv lhs' rhs')

-- Given abs, rep, and 'fix g' expressions, build "rep (abs (fix g)) = fix g"
wwFusionQuantifiedT :: MonadCatch m => CoreExpr -> CoreExpr -> CoreExpr -> Transform c m x Quantified
wwFusionQuantifiedT absE repE fixgE = prefixFailMsg "Building worker/wrapper fusion lemma failed: " $ do
    protoLhs <- buildApplicationM repE =<< buildApplicationM absE fixgE
    let (tvs, lhs) = collectTyBinders protoLhs
    -- This way, the rhs is applied to the proper type variables.
    rhs <- case lhs of
            (App _ (App _ rhs)) -> return rhs
            _                   -> fail "lhs malformed"
    return $ Quantified tvs (Equiv lhs rhs)

-- Perform the worker/wrapper split using condition 1-beta, introducing
-- an unproven lemma for assumption C, and an appropriate w/w fusion lemma.
split1BetaR :: ( BoundVars c, HasHermitMEnv m, HasHscEnv m, HasLemmas m
               , MonadCatch m, MonadIO m, MonadThings m, MonadUnique m )
            => LemmaName -> CoreExpr -> CoreExpr -> Rewrite c m CoreExpr
split1BetaR nm absE repE = do
    (_fixId, [_tyA, f]) <- callNameT $ fromString "Data.Function.fix"

    g <- prefixFailMsg "building (rep . f . abs) failed: "
       $ buildCompositionT repE =<< buildCompositionT f absE
    gId <- constT $ newIdH "g" $ exprType g

    workRhs <- buildFixT $ varToCoreExpr gId
    workId <- constT $ newIdH "worker" $ exprType workRhs

    newRhs <- prefixFailMsg "building (abs work) failed: "
            $ buildApplicationM absE (varToCoreExpr workId)

    assumptionQ <- assumptionCQuantifiedT absE repE f
    insertLemmaT (fromString (show nm ++ "-assumption")) $ Lemma assumptionQ False True -- unproven, used

    wwFusionQ <- wwFusionQuantifiedT absE repE workRhs
    insertLemmaT (fromString (show nm ++ "-fusion")) $ Lemma wwFusionQ True False -- proven (assumed), unused

    return $ mkCoreLets [NonRec gId g, NonRec workId workRhs] newRhs

split2BetaR :: ( BoundVars c, HasHermitMEnv m, HasHscEnv m, HasLemmas m
               , MonadCatch m, MonadIO m, MonadThings m, MonadUnique m )
            => LemmaName -> CoreExpr -> CoreExpr -> Rewrite c m CoreExpr
split2BetaR nm absE repE = do
    (_fixId, [_tyA, f]) <- callNameT $ fromString "Data.Function.fix"
    fixfE <- idR

    repFixFE <- buildApplicationM repE fixfE
    workId <- constT $ newIdH "worker" $ exprType repFixFE

    newRhs <- buildApplicationM absE (varToCoreExpr workId)

    assumptionQ <- assumptionCQuantifiedT absE repE f
    insertLemmaT (fromString (show nm ++ "-assumption")) $ Lemma assumptionQ False True -- unproven, used

    wwFusionQ <- wwFusionQuantifiedT absE repE (varToCoreExpr workId)
    insertLemmaT (fromString (show nm ++ "-fusion")) $ Lemma wwFusionQ True False -- proven (assumed), unused

    return $ mkCoreLets [NonRec workId repFixFE] newRhs
