{-# LANGUAGE FlexibleContexts, TemplateHaskell, RankNTypes #-}
module HERMIT.Optimization.StreamFusion.Vector (plugin, fixStep, Size.Size(..)) where

import           Control.Arrow
import           Control.Monad

import           Data.Maybe (fromMaybe)
import qualified Data.Vector as V
-- import qualified Data.Vector.Generic as G
import qualified Data.Vector.Fusion.Stream as VS
import qualified Data.Vector.Fusion.Stream.Monadic as M
import qualified Data.Vector.Fusion.Stream.Size as Size

import           HERMIT.Core
import           HERMIT.External
import           HERMIT.GHC hiding (display)
import           HERMIT.Kure
import           HERMIT.Monad
import           HERMIT.Optimize
import           HERMIT.Plugin

import           HERMIT.Dictionary

import qualified Language.Haskell.TH as TH

import HERMIT.Optimization.StreamFusion (inlineConstructors)

-- Fix the ordering of type arguments and avoid dealing with size
fixStep :: forall a b m s. Monad m => a -> m (VS.Step s b) -> m (VS.Step (a,s) b)
fixStep a mr = mr >>= return . go
    where go VS.Done        = VS.Done
          go (VS.Skip s)    = VS.Skip (a,s)
          go (VS.Yield b s) = VS.Yield b (a,s)
{-# INLINE fixStep #-}

plugin :: Plugin
plugin = optimize $ \ opts -> do
    let (pn,opts') = fromMaybe (0,opts) (getPhaseFlag opts)
    done <- liftM phasesDone getPhaseInfo
    when (notNull done) $ liftIO $ print $ last done
    run $ promoteR
        $ tryR
        $ repeatR
        $ anyCallR
        $ promoteExprR
        $ (bracketR "concatMap -> flatten" concatMapSafe) <+ unfoldNamesR ['VS.concatMap, 'M.concatMap, 'V.concatMap]
    forM_ opts' $ \ nm -> do
        run $ promoteR $ tryR $ innermostR (promoteR (inlineFunctionWithTyConArgR (TH.mkName nm))) >+> simplifyR
    -- interactive sfexts []
    before SpecConstr $ run $ promoteR $ tryR $ inlineConstructors
    lastPhase $ interactive sfexts []

concatMapSafe :: RewriteH CoreExpr
concatMapSafe = concatMapSR >>> ((lintExprT >>= \_ -> traceR "Success!") <+ traceR "Failed On Lint")

sfexts :: [External]
sfexts =
    [ external "concatmap" (promoteExprR concatMapSR :: RewriteH Core)
        [ "special rule for concatmap" ]
    , external "simp-step" (simpStep :: RewriteH Core)
        [ "special rule for concatmap lambda" ]
    , external "extract-show" (promoteExprT (constT getDynFlags >>= \ dfs -> callDataConNameT 'M.Stream >>> arr (showPpr dfs)) :: TranslateH Core String) []
    , external "inline-dictionaries" (promoteExprR . inlineFunctionWithTyConArgR :: TH.Name -> RewriteH Core) []
    ]

inlineFunctionWithTyConArgR :: TH.Name -> RewriteH CoreExpr
inlineFunctionWithTyConArgR nm = bracketR "inline dictionary" $ do
    -- this will fail if named TyCon is not a dictionary argument
    varT (arr idType >>> onetdT (funTyT (tyConG nm) successT const))
    inlineR

tyConG :: TH.Name -> TranslateH Type ()
tyConG name = do
    nm <- tyConAppT (arr tyConName) (const successT) const
    guardMsg (name `cmpTHName2Name` nm) "not a matching Tycon."

concatMapSR :: RewriteH CoreExpr
concatMapSR = do
    -- concatMapM :: forall a m b. Monad m -> (a -> m (Stream m b)) -> Stream m a -> Stream m b
    (_, [aTy, mTy, bTy, mDict, f]) <- callNameT 'M.concatMapM

    (cxt, v, vs, n', st'') <- return f >>> ensureLam >>> exposeInnerStreamT
    st <- return st'' >>> tryR (extractR sfSimp)
    n@(Lam s _) <- return n' >>> tryR (extractR sfSimp) >>> ensureLam

    flattenSid <- findIdT 'M.flatten
    fixStepid <- findIdT 'fixStep
    unknownid <- findIdT 'Size.Unknown

    let stash = mkCoreTup $ map varToCoreExpr vs
        st' = mkCoreTup [stash, st]
    stId <- constT $ newIdH "st" (exprType st')
    wild <- constT $ cloneVarH ("wild_"++) stId
    stashId <- constT $ newIdH "stash" (exprType stash)
    wild' <- constT $ cloneVarH ("wild_"++) stashId

        -- fixStep :: forall a b m s. Monad m -> a -> m (VS.Step s b) -> m (VS.Step (a,s) b)
    let fixApp = mkCoreApps (varToCoreExpr fixStepid)
                            [ Type (exprType stash), bTy, mTy, Type (exprType st), mDict
                            , stash, mkCoreApp n (varToCoreExpr s) ]
        innerCase = mkSmallTupleCase vs fixApp wild' (varToCoreExpr stashId)
        nFn = mkCoreLams [stId] $
                mkSmallTupleCase [stashId,s] innerCase wild (varToCoreExpr stId)
        mkFn = mkCoreLams [v] $ cxt st'

    -- flatten :: forall a m s b. Monad m -> (a -> m s) -> (s -> m (Step s b)) -> Size -> Stream m a -> Stream m b
    return $ mkCoreApps (varToCoreExpr flattenSid)
                        [ aTy, mTy, Type (exprType st'), bTy
                        , mDict, mkFn, nFn, varToCoreExpr unknownid]

-- | Getting the inner stream.
exposeInnerStreamT
    :: TranslateH CoreExpr ( CoreExpr -> CoreExpr -- monadic context of inner stream
                           , Var        -- the 'x' in 'concatMap (\x -> ...) ...'
                           , [Var]      -- list of captured variables to put in state
                           , CoreExpr   -- inner stream stepper function
                           , CoreExpr ) -- inner stream state
exposeInnerStreamT = lamT idR getDC $ \ v (cxt, [_sTy, g, st, _sz], fvs, vs) ->
                                            (cxt, v, if v `elem` fvs then (v:vs) else vs, g, st)

getDC :: TranslateH CoreExpr ( CoreExpr -> CoreExpr -- context of DC
                             , [CoreExpr], [Var], [Var] )
getDC = getDCFromReturn <+ getDCFromBind

getDCFromBind :: TranslateH CoreExpr ( CoreExpr -> CoreExpr -- context of DC
                                     , [CoreExpr], [Var], [Var] )
getDCFromBind = go <+ (extractR simpStep >>> getDCFromBind)
    where go = do (b, [mTy, mDict, aTy, _bTy, lhs, rhs]) <- callNameT '(>>=)
                  (x, (cxt, args, fvs, xs)) <- return rhs >>> ensureLam >>> lamT idR getDC (,)
                  return (\e -> let e' = cxt e
                                in mkCoreApps b [mTy, mDict, aTy, Type (exprType e), lhs, Lam x e']
                         , args, fvs, if x `elem` fvs then (x:xs) else xs)

ensureLam :: RewriteH CoreExpr
ensureLam = tryR (extractR simplifyR) >>> (lamAllR idR idR <+ etaExpandR "x")

getDCFromReturn :: TranslateH CoreExpr ( CoreExpr -> CoreExpr
                                       , [CoreExpr], [Var], [Var] )
getDCFromReturn = go <+ (extractR simpStep >>> getDCFromReturn)
    where go = do (r, [mTy, mDict, _aTy, dcExp]) <- callNameT 'return
                  (args, fvs) <- return dcExp >>> getDataConInfo
                  return (\e -> mkCoreApps r [mTy, mDict, Type (exprType e), e]
                         , args, fvs, [])

-- | Return list of arguments to Stream (existential, generator, state)
--   along with list of free variables.
getDataConInfo :: TranslateH CoreExpr ([CoreExpr], [Var])
getDataConInfo = go <+ (extractR simpStep >>> getDataConInfo)
    where go = do (_dc, _tys, args) <- callDataConNameT 'M.Stream
                  fvs <- arr $ varSetElems . freeVarsExpr
                  return (args, fvs)

-- Simplification
sfSimp :: RewriteH Core
sfSimp = repeatR simpStep

simpStep :: RewriteH Core
simpStep =    simplifyR
           <+ (onetdR (promoteExprR (   letUnfloatR
                                     <+ caseElimR
                                     <+ elimExistentials
                                     <+ (caseUnfloatR >>> appAllR idR idR))))
           <+ promoteExprR unfoldR

elimExistentials :: RewriteH CoreExpr
elimExistentials = do
    Case _s _bnd _ty alts <- idR
    guardMsg (notNull [ v | (_,vs,_) <- alts, v <- vs, isTyVar v ])
             "no existential types in patterns"
    caseAllR (extractR sfSimp) idR idR (const idR) >>> {- observeR "before reduce" >>> -} caseReduceR -- >>> observeR "result"

-- this currently slows things down, probably because of uneliminated streams/unstreams
-- need to implement rules to convert generic vector functions to stream equivalents and
-- the stream/unstream and unstream/stream rules akin to the list optimization
--                                                  <+ rule "genericConcatMap")))
-- {-# RULES "genericConcatMap" [~] forall f. G.concatMap f = G.unstream . VS.concatMap (G.stream . f) . G.stream #-}

