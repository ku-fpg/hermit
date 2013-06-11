{-# LANGUAGE TemplateHaskell, RankNTypes #-}
module HERMIT.Optimization.StreamFusion.Vector (plugin, fixStep) where

import Control.Arrow

import GhcPlugins

import Language.HERMIT.Core
import Language.HERMIT.Dictionary -- for bash
import Language.HERMIT.External
import Language.HERMIT.Kure
import Language.HERMIT.Monad
import Language.HERMIT.Optimize

import Language.HERMIT.Primitive.Common
import Language.HERMIT.Primitive.Debug hiding (externals)
import Language.HERMIT.Primitive.GHC hiding (externals)
import Language.HERMIT.Primitive.Local hiding (externals)
import Language.HERMIT.Primitive.New hiding (externals)
import Language.HERMIT.Primitive.Unfold hiding (externals)

import qualified Data.Vector as V
import qualified Data.Vector.Generic as G
import qualified Data.Vector.Fusion.Stream as VS
import qualified Data.Vector.Fusion.Stream.Monadic as M
import qualified Data.Vector.Fusion.Stream.Size as Size

-- Fix the ordering of type arguments and avoid dealing with size
fixStep :: forall a b m s. Monad m => a -> m (VS.Step s b) -> m (VS.Step (a,s) b)
fixStep a mr = mr >>= return . go
    where go VS.Done        = VS.Done
          go (VS.Skip s)    = VS.Skip (a,s)
          go (VS.Yield b s) = VS.Yield b (a,s)
{-# INLINE fixStep #-}

plugin :: Plugin
plugin = optimize $ \ opts -> phase 0 $ do
    run $ tryR $     bashR externals
                 >+> repeatR (anyCallR (promoteExprR (   concatMapSR
                                                      <+ unfoldAnyR ['VS.concatMap, 'M.concatMap, 'V.concatMap]
                                                      <+ rule "genericConcatMap")))
--                 >+> bashR externals -- causes 'occurance of dead Id' core lint error!
    interactive sfexts opts

-- this currently slows things down, probably because of uneliminated streams/unstreams
-- need to implement rules to convert generic vector functions to stream equivalents and
-- the stream/unstream and unstream/stream rules akin to the list optimization
-- {-# RULES "genericConcatMap" [~] forall f. G.concatMap f = G.unstream . VS.concatMap (G.stream . f) . G.stream #-}

sfexts :: [External]
sfexts =
    [ external "concatmap" (promoteExprR concatMapSR :: RewriteH Core)
        [ "special rule for concatmap" ]
    , external "expose-stream" (floatAppOut :: RewriteH Core)
        [ "special rule for concatmap lambda" ]
    , external "extract-show" (promoteExprT (constT getDynFlags >>= \ dfs -> callDataConNameT 'M.Stream >>> arr (showPpr dfs)) :: TranslateH Core String) []
    ]

concatMapSR :: RewriteH CoreExpr
concatMapSR = do
    -- concatMapM :: forall a m b. Monad m -> (a -> m (Stream m b)) -> Stream m a -> Stream m b
    (_, [aTy, mTy, bTy, mDict, f]) <- callNameT 'M.concatMapM

    (v, n', st) <- applyInContextT exposeInnerStreamT f
    n@(Lam s _) <- applyInContextT (lamAllR idR idR <+ etaExpand "s") n'

    flattenSid <- findIdT 'M.flatten
    fixStepid <- findIdT 'fixStep
    returnid <- findIdT 'return
    unknownid <- findIdT 'Size.Unknown

    let st' = mkCoreTup [varToCoreExpr v, st]
    stId <- constT $ newIdH "st" (exprType st')
    wild <- constT $ cloneVarH ("wild_"++) stId

        -- fixStep :: forall a b m s. Monad m -> a -> m (VS.Step s b) -> m (VS.Step (a,s) b)
    let fixApp = mkCoreApps (varToCoreExpr fixStepid)
                            [ aTy, bTy, mTy, Type $ exprType st, mDict
                            , varToCoreExpr v, mkCoreApp n (varToCoreExpr s) ]
        nFn = mkCoreLams [stId] $
                mkSmallTupleCase [v,s] fixApp wild (varToCoreExpr stId)
        -- return :: forall m. Monad m -> (forall a. a -> m a)
        mkFn = mkCoreLams [v] $ mkCoreApps (varToCoreExpr returnid) [mTy, mDict, Type $ exprType st', st']

    -- flatten :: forall a m s b. Monad m -> (a -> m s) -> (s -> m (Step s b)) -> Size -> Stream m a -> Stream m b
    return $ mkCoreApps (varToCoreExpr flattenSid)
                        [ aTy, mTy, Type (exprType st'), bTy
                        , mDict, mkFn, nFn, varToCoreExpr unknownid]

exposeInnerStreamT
    :: TranslateH CoreExpr ( CoreBndr   -- the 'x' in 'concatMap (\x -> ...) ...'
                           , CoreExpr   -- inner stream stepper function
                           , CoreExpr ) -- inner stream state
exposeInnerStreamT =
   (lamT idR getDCFromReturn (\ v (_dc, _univTys, [_sTy, n, st, _sz]) -> (v, n, st)))
    <+ ((unfoldR <+ letElim <+ letUnfloat <+ caseElim <+ caseUnfloat) >>> exposeInnerStreamT)

getDCFromReturn :: TranslateH CoreExpr (DataCon, [Type], [CoreExpr])
getDCFromReturn =
    (do (_r, [_aTy, _mTy, _mDict, dcExp]) <- callNameT 'return
        applyInContextT getDataConInfo dcExp) <+ (extractR floatAppOut >>> getDCFromReturn)

getDataConInfo :: TranslateH CoreExpr (DataCon, [Type], [CoreExpr])
getDataConInfo = (callDataConNameT 'M.Stream) <+ (extractR floatAppOut >>> getDataConInfo)

floatAppOut :: RewriteH Core
floatAppOut = onetdR (promoteExprR $ letElim <+ letUnfloat <+ caseElim <+ caseUnfloat)
              <+ simplifyR <+ promoteExprR unfoldR
