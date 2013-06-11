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

import qualified Data.Vector.Fusion.Stream as VS
import qualified Data.Vector.Fusion.Stream.Monadic as M
import qualified Data.Vector.Fusion.Stream.Size as Size
import qualified Data.Vector.Fusion.Util as Util

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
--                 >+> myanybuR (concatMapSR 'VS.concatMap 'VS.flatten)
--                 >+> repeatR (anyCallR $ promoteExprR $ unfoldNameR 'fixStep)
--                 >+> bashR externals
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
    , external "expose-stream" (floatAppOut :: RewriteH Core)
        [ "special rule for concatmap lambda" ]
    , external "extract-show" (promoteExprT (constT getDynFlags >>= \ dfs -> callDataConNameT 'M.Stream >>> arr (showPpr dfs)) :: TranslateH Core String) []
    ]

concatMapSR :: RewriteH CoreExpr
concatMapSR = do
    -- concatMapM :: forall a m b. Monad m -> (a -> m (Stream m b)) -> Stream m a -> Stream m b
    (_, [aTy, mTy, bTy, mDict, f]) <- callNameT 'M.concatMapM

    _ <- applyInContextT (observeR "f") f
    (v, n', st, _sz) <- applyInContextT exposeInnerStreamT f
    _ <- applyInContextT (observeR "n'") n'
    _ <- applyInContextT (observeR "st") st
--    _ <- applyInContextT (observeR "sz") _sz
    n@(Lam s _) <- applyInContextT (extractR $ repeatR floatAppOut) n'
    _ <- applyInContextT (observeR "n") n

    flattenSid <- findIdT 'M.flatten
    fixStepid <- findIdT 'fixStep
    returnid <- findIdT 'return
    unknownid <- findIdT 'Size.Unknown
    _ <- applyInContextT (observeR "unknown") (varToCoreExpr unknownid :: CoreExpr)

    let st' = mkCoreTup [varToCoreExpr v, st]
    stId <- constT $ newIdH "st" (exprType st')
    wild <- constT $ cloneVarH ("wild_"++) stId

    _ <- applyInContextT (observeR "st'") st'

        -- fixStep :: forall a b m s. Monad m -> a -> m (VS.Step s b) -> m (VS.Step (a,s) b)
    let fixApp = mkCoreApps (varToCoreExpr fixStepid)
                            [ aTy, bTy, mTy, Type $ exprType st, mDict
                            , varToCoreExpr v, mkCoreApp n (varToCoreExpr s) ]
        nFn = mkCoreLams [stId] $
                mkSmallTupleCase [v,s] fixApp wild (varToCoreExpr stId)
        -- return :: forall m. Monad m -> (forall a. a -> m a)
        mkFn = mkCoreLams [v] $ mkCoreApps (varToCoreExpr returnid) [mTy, mDict, Type $ exprType st', st']

    _ <- applyInContextT (observeR "fixApp") fixApp
    _ <- applyInContextT (observeR "nFn") nFn
    _ <- applyInContextT (observeR "return type") (Type $ varType returnid :: CoreExpr)
    _ <- applyInContextT (observeR "mkFn") mkFn

    -- flatten :: forall a m s b. Monad m -> (a -> m s) -> (s -> m (Step s b)) -> Size -> Stream m a -> Stream m b
    return (mkCoreApps (varToCoreExpr flattenSid)
                       [ aTy, mTy, Type (exprType st'), bTy
                       , mDict, mkFn, nFn, varToCoreExpr unknownid]) >>> observeR "result"

exposeInnerStreamT
    :: TranslateH CoreExpr ( CoreBndr   -- the 'x' in 'concatMap (\x -> ...) ...'
                           , CoreExpr   -- inner stream stepper function
                           , CoreExpr   -- inner stream state
                           , CoreExpr ) -- inner stream size
exposeInnerStreamT =
   (lamT idR getDCFromReturn (\ v (_dc, _univTys, [_sTy, n, st, sz]) -> (v, n, st, sz)))
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
