module HERMIT.Optimization.StreamFusion (plugin) where

import Control.Arrow

import GhcPlugins

import Language.HERMIT.Core
import Language.HERMIT.Dictionary -- for bash
import Language.HERMIT.External -- for bash
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
    run $ tryR $ repeatR (myanybuR (rules ["foldlS", "concatMapS", "mapS", "enumFromToS", "filterS", "zipS", "stream/unstream", "unstream/stream"])
                         <+ bash)
                 >>> tryR (myanybuR concatMapSR)
                 >>> repeatR (anyCallR $ promoteExprR $ unfoldAnyR $ map TH.mkName ["fixStep", "foldlS", "flattenS", "mapS", "enumFromToS", "filterS", "zipS"])
                 >>> bash
    interactive externals opts

-- | A fixed-point traveral, starting with the innermost term.
myinnermostR :: (Walker c g, MonadCatch m, Injection a g) => Rewrite c m a -> Rewrite c m g
myinnermostR r = setFailMsg "innermostR failed" $
    let go = myanybuR (promoteR r >>> tryR go)
    in go
{-# INLINE myinnermostR #-}

-- | Apply a 'Rewrite' in a bottom-up manner, succeeding if any succeed.
myanybuR :: (Walker c g, MonadCatch m, Injection a g) => Rewrite c m a -> Rewrite c m g
myanybuR r = setFailMsg "anybuR failed" $
    let go = anyR go >+> promoteR r
    in go
{-# INLINE myanybuR #-}

bash :: RewriteH Core
bash = metaCmd (all_externals externals) Bash (setFailMsg "Nothing to do." . myinnermostR . orR)

externals :: [External]
externals =
    [ external "concatmap" (promoteExprR concatMapSR :: RewriteH Core)
        [ "special rule for concatmap" ]
    ]

concatMapSR :: RewriteH CoreExpr
concatMapSR = do
    (_, [aTy, bTy, f, outerStream]) <- callNameT (TH.mkName "concatMapS")

    c <- contextT
    (v, n@(Lam s _), st) <- constT $ apply exposeInnerStreamT c f

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
                        [ Type (exprType st'), bTy, aTy
                        , nFn, Lam v st', outerStream ]

exposeInnerStreamT
    :: TranslateH CoreExpr ( CoreBndr   -- the 'x' in 'concatMap (\x -> ...) ...'
                           , CoreExpr   -- inner stream stepper function
                           , CoreExpr ) -- inner stream state
exposeInnerStreamT =
   (lamR exposeStreamConstructor >>>
    lamT (callDataConNameT $ TH.mkName "Stream")
         (\ v (_dc, _univTys, [_sTy, n, st]) -> (v, n, st)))
    <+ (unfoldR >>> exposeInnerStreamT)

exposeStreamConstructor :: RewriteH CoreExpr
exposeStreamConstructor = tryR $ extractR $ repeatR $
    onetdR (promoteExprR $ rules ["stream/unstream", "unstream/stream"]
                           <+ letUnfloat <+ letElim <+ caseUnfloat)
     <+ simplifyR <+ promoteExprR unfoldR
