module HERMIT.Optimization.StreamFusion (plugin) where

import Control.Arrow

import GhcPlugins

import Language.HERMIT.Core
import Language.HERMIT.Dictionary -- for bash
import Language.HERMIT.External
import Language.HERMIT.Kure
import Language.HERMIT.Monad
import Language.HERMIT.Optimize

import Language.HERMIT.Primitive.Common
import Language.HERMIT.Primitive.GHC hiding (externals)
import Language.HERMIT.Primitive.Local hiding (externals)
import Language.HERMIT.Primitive.New hiding (externals)
import Language.HERMIT.Primitive.Unfold hiding (externals)

import Language.Haskell.TH as TH

plugin :: Plugin
plugin = optimize $ \ opts -> phase 0 $ do
{-
    run $ tryR $ repeatR (myanybuR (rules ["foldlS", "concatMapS", "mapS", "enumFromToS", "filterS", "zipS", "stream/unstream", "unstream/stream"])
                         <+ bashR externals)
                 >>> tryR (myanybuR concatMapSR)
                 >>> repeatR (anyCallR $ promoteExprR $ unfoldAnyR $ map TH.mkName ["fixStep", "foldlS", "flattenS", "mapS", "enumFromToS", "filterS", "zipS"])
                 >>> bashR externals
-}
    interactive sfexts opts

-- | Apply a 'Rewrite' in a bottom-up manner, succeeding if any succeed.
myanybuR :: (Walker c g, MonadCatch m, Injection a g) => Rewrite c m a -> Rewrite c m g
myanybuR r = setFailMsg "anybuR failed" $
    let go = anyR go >+> promoteR r
    in go
{-# INLINE myanybuR #-}

sfexts :: [External]
sfexts =
    [ external "concatmap" (promoteExprR concatMapSR :: RewriteH Core)
        [ "special rule for concatmap" ]
    ]

concatMapSR :: RewriteH CoreExpr
concatMapSR = do
    (_, [aTy, bTy, f, outerStream]) <- callNameT (TH.mkName "concatMapS")

    (v, n@(Lam s _), st) <- applyInContextT exposeInnerStreamT f

    flattenSid <- findIdT $ TH.mkName "flattenS"
    fixStepid <- findIdT $ TH.mkName "fixStep"

    let st' = mkCoreTup [varToCoreExpr v, st]
    stId <- constT $ newIdH "st" (exprType st')
    wild <- constT $ cloneVarH ("wild_"++) stId

    let fixApp = mkCoreApps (varToCoreExpr fixStepid)
                            [ aTy, bTy, Type $ exprType st
                            , varToCoreExpr v, mkCoreApp n (varToCoreExpr s) ]
        nFn = mkCoreLams [stId] $
                mkSmallTupleCase [v,s] fixApp wild (varToCoreExpr stId)

    return $ mkCoreApps (varToCoreExpr flattenSid)
                        [ aTy, bTy, Type (exprType st')
                        , nFn, Lam v st', outerStream ]

exposeInnerStreamT
    :: TranslateH CoreExpr ( CoreBndr   -- the 'x' in 'concatMap (\x -> ...) ...'
                           , CoreExpr   -- inner stream stepper function
                           , CoreExpr ) -- inner stream state
exposeInnerStreamT =
   (lamT idR (exposeStreamConstructor >>> callDataConNameT (TH.mkName "Stream"))
         (\ v (_dc, _univTys, [_sTy, n, st]) -> (v, n, st)))
    <+ (unfoldR >>> exposeInnerStreamT)

exposeStreamConstructor :: RewriteH CoreExpr
exposeStreamConstructor = tryR $ extractR $ repeatR $
    onetdR (promoteExprR $ rules ["stream/unstream", "unstream/stream"]
                           <+ letElim <+ letUnfloat <+ caseElim <+ caseUnfloat)
     <+ simplifyR <+ promoteExprR unfoldR
