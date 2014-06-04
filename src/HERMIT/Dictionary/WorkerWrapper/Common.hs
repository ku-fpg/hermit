{-# LANGUAGE DeriveDataTypeable, TypeFamilies #-}
module HERMIT.Dictionary.WorkerWrapper.Common
    ( WWAssumptionTag(..)
    , WWAssumption(..)
    , assumptionEqualityT
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

import HERMIT.Dictionary.Fold
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

breakFunTyM :: Monad m => Type -> m ([TyVar], Type, Type)
breakFunTyM ty = do
    let (tvs, fTy) = splitForAllTys ty
    (argTy, resTy) <- splitFunTypeM fTy
    return (tvs, argTy, resTy)

assumptionEqualityT :: WWAssumptionTag -> CoreString -> CoreString -> TransformH x CoreExprEquality
assumptionEqualityT A = assumptionAEqualityT
assumptionEqualityT B = assumptionBEqualityT
assumptionEqualityT C = assumptionCEqualityT

assumptionAEqualityT :: CoreString -> CoreString -> TransformH x CoreExprEquality
assumptionAEqualityT absC repC = do
    absE <- parseCoreExprT absC
    repE <- parseCoreExprT repC
    (vsR, domR, codR) <- breakFunTyM (exprType repE)
    (vsA, domA, _) <- breakFunTyM (exprType absE)
    sub <- maybe (fail "codomain of rep and domain of abs do not unify") return
                 (unifyTypes vsR codR domA)
    let (tvs, tys) = unzip sub
        vsR' = filter (`notElem` tvs) vsR -- things we should stick back on as foralls
        xTy = substTyWith tvs tys $ mkForAllTys vsR' domR
    xId <- constT $ newIdH "x" xTy
    let rhsE    = varToCoreExpr xId
        repAppE = mkCoreApps repE $ [ case lookup v sub of
                                        Nothing -> varToCoreExpr v
                                        Just ty -> Type ty
                                    | v <- vsR ] ++ [rhsE]
        lhsE    = mkCoreApps absE $ map varToCoreExpr vsA ++ [repAppE]
    return $ CoreExprEquality (vsA ++ vsR' ++ [xId]) lhsE rhsE

assumptionBEqualityT :: CoreString -> CoreString -> TransformH x CoreExprEquality
assumptionBEqualityT _ _ = fail "assumption B generation not implemented"

assumptionCEqualityT :: CoreString -> CoreString -> TransformH x CoreExprEquality
assumptionCEqualityT _ _ = fail "assumption C generation not implemented"
