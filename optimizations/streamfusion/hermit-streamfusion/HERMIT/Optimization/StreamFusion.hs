module HERMIT.Optimization.StreamFusion (plugin) where

import Control.Arrow

import GhcPlugins

import HERMIT.External
import HERMIT.Kure
import HERMIT.Monad
import HERMIT.Optimize

import HERMIT.Dictionary

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
                           <+ letElimR <+ letUnfloatR <+ caseElimR <+ caseUnfloatR)
     <+ simplifyR <+ promoteExprR unfoldR
