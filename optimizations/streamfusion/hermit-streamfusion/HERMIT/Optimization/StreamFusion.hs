module HERMIT.Optimization.StreamFusion (plugin, inlineConstructors) where

import Control.Arrow
import Control.Monad

import Data.List (partition)

import HERMIT.External
import HERMIT.GHC
import HERMIT.Kure
import HERMIT.Monad
import HERMIT.Optimize
import HERMIT.Plugin

import HERMIT.Dictionary

import qualified Language.Haskell.TH as TH

import Prelude hiding (until)

plugin :: Plugin
plugin = optimize $ \ opts -> do
    let (os,cos) = partition (`elem` ["interactive","inline","rules"]) opts
    phase 0 $ do
        when ("interactive" `elem` os) $ phase 0 $ interactive sfexts cos
        -- We need to run the rules which match on standard list combinators
        -- before the simplifier tries to use the rules that belong to them.
        when ("rules" `elem` os) $ run
                                 $ promoteR
                                 $ tryR
                                 $ simplifyR
                                   >+> (repeatR (onetdR $ promoteExprR $ bracketR "rule" $ rules (filter (`notElem` ["consS", "nilS", "singletonS"]) allRules))
                                        <+ simplifyR)
    run $ promoteR
        $ tryR
        $ repeatR
        $ anyCallR
        $ promoteExprR
        $ bracketR "concatmap -> flatten"
        $ concatMapSR
    when ("inline" `elem` os) $ before SpecConstr $ run $ promoteR $ tryR $ inlineConstructors
    when ("interactive" `elem` os) $ lastPhase $ interactive sfexts cos

inlineConstructors :: RewriteH Core
inlineConstructors = do
    let nonRecTypeDCT = do
            (dc,_tys,_args) <- callDataConT
            guardMsg (not $ any (`eqType` dataConOrigResTy dc) (dataConOrigArgTys dc)) "constructor is recursive"
            return ()
    -- get all the bindings to constructor RHSs
    vs <- collectT (promoteT $ nonRecT idR nonRecTypeDCT const)
    -- transitively get all the bindings to those bindings (rare?)
    let transT vs = tryM vs $ do
            vs' <- collectT (promoteT $ nonRecT (whenM (arr (`notElem` vs)) idR) (varT (arr (`elem` vs))) const)
            guardMsg (notNull vs') "no new bindings"
            transT vs'

    vs' <- transT vs
    innermostR (promoteR $ bracketR "inlining constructor" $ whenM (varT (arr (`elem` vs'))) inlineR)

-- TODO: slurp these somehow? Need FastString tables to sync
allRules :: [String]
allRules =
    [ "concat/concatMap" -- important this is first
    , "stream/unstream"
    , "unstream/stream"
    , "appendS"
    , "concatMapS"
    , "consS"
    , "enumFromToS"
    , "filterS"
    , "foldlS"
    , "foldlS'"
    , "foldrS"
    , "headS"
    , "iterateS"
    , "lengthS"
    , "mapS"
    , "nilS"
    , "singletonS"
    , "tailS"
    , "zipS"
    , "zipWithS"
    ]

sfexts :: [External]
sfexts =
    [ external "concatmap" (promoteExprR concatMapSR :: RewriteH Core)
        [ "special rule for concatmap" ]
    , external "all-rules" (repeatR (onetdR $ promoteExprR $ rules allRules) :: RewriteH Core)
        [ "apply all the concatMap rules" ]
    , external "simp-step" (simpStep :: RewriteH Core)
        [ "do one step of simplification" ]
    ]

concatMapSR :: RewriteH CoreExpr
concatMapSR = do
    -- concatMapS :: forall a b. (a -> Stream b) -> Stream a -> Stream b
    (_, [aTy, bTy, f]) <- callNameT (TH.mkName "concatMapS")

    (v, n', st'') <- return f >>> ensureLam >>> exposeInnerStreamT
    st <- return st'' >>> tryR (extractR sfSimp)
    n@(Lam s _) <- return n' >>> tryR (extractR sfSimp) >>> ensureLam

    flattenSid <- findIdT $ TH.mkName "flattenS"
    fixStepid <- findIdT $ TH.mkName "fixStep"

    let st' = mkCoreTup [varToCoreExpr v, st]
    stId <- constT $ newIdH "st" (exprType st')
    wild <- constT $ cloneVarH ("wild_"++) stId

        -- fixStep :: forall a b s. a -> Step b s -> Step b (a,s)
    let fixApp = mkCoreApps (varToCoreExpr fixStepid)
                            [ aTy, bTy, Type (exprType st)
                            , varToCoreExpr v, mkCoreApp n (varToCoreExpr s) ]
        nFn = mkCoreLams [stId] $
                mkSmallTupleCase [v,s] fixApp wild (varToCoreExpr stId)
        mkFn = mkCoreLams [v] st'

    -- flattenS :: forall a b s. (a -> s) -> (s -> Step b s) -> Stream a -> Stream b
    return $ mkCoreApps (varToCoreExpr flattenSid)
                        [ aTy, bTy, Type (exprType st'), mkFn, nFn ]

-- | Getting the inner stream.
exposeInnerStreamT
    :: TranslateH CoreExpr ( Var        -- the 'x' in 'concatMap (\x -> ...) ...'
                           , CoreExpr   -- inner stream stepper function
                           , CoreExpr ) -- inner stream state
exposeInnerStreamT = lamT idR getDataConInfo $ \ v [_sTy, g, st] -> (v, g, st)

ensureLam :: RewriteH CoreExpr
ensureLam = tryR (extractR simplifyR) >>> (lamAllR idR idR <+ etaExpandR "x")

-- | Return list of arguments to Stream (existential, generator, state)
getDataConInfo :: TranslateH CoreExpr [CoreExpr]
getDataConInfo = go <+ (tryR (caseFloatArgR Nothing >>> extractR (anyCallR (promoteR (rule "stream/unstream")))) >>> extractR simpStep >>> getDataConInfo)
    where go = do (_dc, _tys, args) <- callDataConNameT $ TH.mkName "Stream"
                  return args

sfSimp :: RewriteH Core
sfSimp = repeatR simpStep

-- TODO: don't unfold recursive functions
simpStep :: RewriteH Core
simpStep =    simplifyR
           <+ onetdR (promoteExprR $ rules allRules)
           <+ (onetdR (promoteExprR (   letUnfloatR
                                     <+ caseElimR
                                     <+ elimExistentials
                                     <+ (caseUnfloatR >>> appAllR idR idR))))
           <+ promoteExprR unfoldR -- last resort, as we don't want to unfold 'stream' before the rule can fire
           <+ fail "simpStep failed"

elimExistentials :: RewriteH CoreExpr
elimExistentials = do
    Case _s _bnd _ty alts <- idR
    guardMsg (notNull [ v | (_,vs,_) <- alts, v <- vs, isTyVar v ])
             "no existential types in patterns"
    caseAllR (extractR sfSimp) idR idR (const idR) >>> {- observeR "before reduce" >>> -} caseReduceR -- >>> observeR "result"

