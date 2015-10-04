{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

module HERMIT.Dictionary.GHC
    ( -- * GHC-based Transformations
      -- | This module contains transformations that are reflections of GHC functions, or derived from GHC functions.
      externals
      -- ** Dynamic Loading
    , loadLemmaLibraryT
    , LemmaLibrary
    , injectDependencyT
      -- ** Substitution
    , substR
      -- ** Utilities
    , dynFlagsT
    , arityOf
      -- ** Lifted GHC capabilities
      -- A zombie is an identifer that has 'OccInfo' 'IAmDead', but still has occurrences.
    , lintExprT
    , lintModuleT
    , lintClauseT
    , occurAnalyseR
    , occurAnalyseChangedR
    , occurAnalyseExprChangedR
    , occurAnalyseAndDezombifyR
    , occurrenceAnalysisR
    , deShadowProgR
    , dezombifyR
    , buildDictionary
    , buildDictionaryT
    , buildTypeable
    ) where

import qualified Bag
import qualified CoreLint
#if __GLASGOW_HASKELL__ > 710 || (__GLASGOW_HASKELL__ == 710 && __GLASGOW_HASKELL_PATCHLEVEL1__ > 2)
import           TcRnMonad (getCtLocM)
import           TcRnTypes (cc_ev)
import           TcSimplify (solveWanteds, runTcS)
#endif

import           Control.Arrow
import           Control.Monad
import           Control.Monad.IO.Class

import           Data.Char (isSpace)
import           Data.List (mapAccumL, nub)
import qualified Data.Map as M
import           Data.String

import           HERMIT.Core
import           HERMIT.Context
import           HERMIT.External
import           HERMIT.GHC
import           HERMIT.Kure
import           HERMIT.Lemma
import           HERMIT.Monad
import           HERMIT.Name

import           HERMIT.PrettyPrinter.Common
import           HERMIT.PrettyPrinter.Glyphs
import qualified HERMIT.PrettyPrinter.Clean as Clean

------------------------------------------------------------------------

-- | Externals that reflect GHC functions, or are derived from GHC functions.
externals :: [External]
externals =
    [ external "deshadow-prog" (promoteProgR deShadowProgR :: RewriteH LCore)
        [ "Deshadow a program." ] .+ Deep
    , external "dezombify" (promoteExprR dezombifyR :: RewriteH LCore)
        [ "Zap the occurrence information in the current identifer if it is a zombie."] .+ Shallow
    , external "occurrence-analysis" (occurrenceAnalysisR :: RewriteH LCore)
        [ "Perform dependency analysis on all sub-expressions; simplifying and updating identifer info."] .+ Deep
    , external "lint-expr" (promoteExprT lintExprT :: TransformH LCoreTC String)
        [ "Runs GHC's Core Lint, which typechecks the current expression."
        , "Note: this can miss several things that a whole-module core lint will find."
        , "For instance, running this on the RHS of a binding, the type of the RHS will"
        , "not be checked against the type of the binding. Running on the whole let expression"
        , "will catch that however."] .+ Deep .+ Debug .+ Query
    , external "lint-module" (promoteModGutsT lintModuleT :: TransformH LCoreTC String)
        [ "Runs GHC's Core Lint, which typechecks the current module."] .+ Deep .+ Debug .+ Query
    , external "lint" (promoteT lintClauseT :: TransformH LCoreTC String)
        [ "Lint check a clause." ]
    , external "load-lemma-library" (flip loadLemmaLibraryT Nothing :: HermitName -> TransformH LCore String)
        [ "Dynamically load a library of lemmas." ]
    , external "load-lemma-library" ((\nm -> loadLemmaLibraryT nm . Just) :: HermitName -> LemmaName -> TransformH LCore String)
        [ "Dynamically load a specific lemma from a library of lemmas." ]
    , external "inject-dependency" (promoteModGutsT . injectDependencyT . mkModuleName :: String -> TransformH LCore ())
        [ "Inject a dependency on the given module." ]
    ]

------------------------------------------------------------------------

-- | Substitute all occurrences of a variable with an expression, in either a program, an expression, or a case alternative.
substR :: MonadCatch m => Var -> CoreExpr -> Rewrite c m Core
substR v e = setFailMsg "Can only perform substitution on expressions, case alternatives or programs." $
             promoteExprR (arr $ substCoreExpr v e) <+ promoteProgR (substTopBindR v e) <+ promoteAltR (arr $ substCoreAlt v e)

-- | Substitute all occurrences of a variable with an expression, in a program.
substTopBindR :: Monad m => Var -> CoreExpr -> Rewrite c m CoreProg
substTopBindR v e =  contextfreeT $ \ p -> do
    -- TODO.  Do we need to initialize the emptySubst with bindFreeVars?
    let emptySub =  emptySubst -- mkEmptySubst (mkInScopeSet (exprFreeVars exp))
    return $ bindsToProg $ snd (mapAccumL substBind (extendSubst emptySub v e) (progToBinds p))

------------------------------------------------------------------------

-- | [from GHC documentation] De-shadowing the program is sometimes a useful pre-pass.
-- It can be done simply by running over the bindings with an empty substitution,
-- becuase substitution returns a result that has no-shadowing guaranteed.
--
-- (Actually, within a single /type/ there might still be shadowing, because
-- 'substTy' is a no-op for the empty substitution, but that's probably OK.)
deShadowProgR :: Monad m => Rewrite c m CoreProg
deShadowProgR = arr (bindsToProg . deShadowBinds . progToBinds)

--------------------------------------------------------

-- | Try to figure out the arity of an identifier.
arityOf :: ReadBindings c => c -> Id -> Int
arityOf c i =
     case lookupHermitBinding i c of
        Nothing       -> idArity i
        -- Note: the exprArity will call idArity if
        -- it hits an id; perhaps we should do the counting
        -- The advantage of idArity is it will terminate, though.
        Just b -> runKureM exprArity
                           (const 0) -- conservative estimate, as we don't know what the expression looks like
                           (hermitBindingExpr b)

-------------------------------------------

-- | Run the Core Lint typechecker.
-- Fails on errors, with error messages.
-- Succeeds returning warnings.
lintModuleT :: TransformH ModGuts String
lintModuleT =
  do dynFlags <- dynFlagsT
     bnds     <- arr mg_binds
#if __GLASGOW_HASKELL__ < 710
     let (warns, errs)    = CoreLint.lintCoreBindings [] bnds -- [] are vars to treat as in scope, used by GHCi
#elif __GLASGOW_HASKELL_PATCHLEVEL1__ <= 2
     -- [] are vars to treat as in scope, used by GHCi
     -- 'CoreDesugar' so we check for global ids, but not INLINE loop breakers, see notes in GHC's CoreLint module.
     let (warns, errs)    = CoreLint.lintCoreBindings CoreDesugar [] bnds
#else
     let (warns, errs)    = CoreLint.lintCoreBindings dynFlags CoreDesugar [] bnds
#endif
         dumpSDocs endMsg = Bag.foldBag (\ d r -> d ++ ('\n':r)) (showSDoc dynFlags) endMsg
     if Bag.isEmptyBag errs
       then return $ dumpSDocs "Core Lint Passed" warns
       else fail $ "Core Lint Failed:\n" ++ dumpSDocs "" errs

-- | Note: this can miss several things that a whole-module core lint will find.
-- For instance, running this on the RHS of a binding, the type of the RHS will
-- not be checked against the type of the binding. Running on the whole let expression
-- will catch that however.
lintExprT :: (BoundVars c, Monad m, HasDynFlags m) => Transform c m CoreExpr String
lintExprT = transform $ \ c e -> do
    dflags <- getDynFlags
    case e of
        Type _ -> fail "cannot core lint types."
        _ -> maybe (return "Core Lint Passed") (fail . showSDoc dflags)
#if __GLASGOW_HASKELL__ < 710 || (__GLASGOW_HASKELL__ == 710 && __GLASGOW_PATCHLEVEL1__ <= 2)
                   (CoreLint.lintExpr (varSetElems $ boundVars c) e)
#else
                   (CoreLint.lintExpr dflags (varSetElems $ boundVars c) e)
#endif

-------------------------------------------

-- | Lifted version of 'getDynFlags'.
dynFlagsT :: HasDynFlags m => Transform c m a DynFlags
dynFlagsT = constT getDynFlags

-------------------------------------------

----------------------------------------------------------------------

-- TODO: Ideally, occurAnalyseExprR would fail if nothing changed.
--       This is tricky though, as it's not just the structure of the expression, but also the meta-data.

-- | Zap the 'OccInfo' in a zombie identifier.
dezombifyR :: (ExtendPath c Crumb, Monad m) => Rewrite c m CoreExpr
dezombifyR = varR (acceptR isDeadBinder >>^ zapVarOccInfo)

-- | Apply 'occurAnalyseExprR' to all sub-expressions.
occurAnalyseR :: (Injection CoreExpr u, Walker c u, MonadCatch m) => Rewrite c m u
occurAnalyseR = let r  = promoteExprR (arr occurAnalyseExpr_NoBinderSwap) -- See Note [No Binder Swap]
                    go = r <+ anyR go
                 in tryR go -- always succeed

{-
  Note [No Binder Swap]

  The binder swap performed by occurrence analysis in GHC <= 7.8.3 is buggy
  in that it can lead to unintended variable capture (Trac #9440). Concretely,
  this will send bash into a loop, or cause core lint to fail. As this is an
  un-expected change as far as HERMIT users are concerned anyway, we use the
  version that doesn't perform the binder swap.
-}

-- | Occurrence analyse an expression, failing if the result is syntactically equal to the initial expression.
occurAnalyseExprChangedR :: MonadCatch m => Rewrite c m CoreExpr
occurAnalyseExprChangedR = changedByR exprSyntaxEq (arr occurAnalyseExpr_NoBinderSwap) -- See Note [No Binder Swap]

-- | Occurrence analyse all sub-expressions, failing if the result is syntactically equal to the initial expression.
occurAnalyseChangedR :: (AddBindings c, ExtendPath c Crumb, HasEmptyContext c, LemmaContext c, ReadPath c Crumb, MonadCatch m) => Rewrite c m LCore
occurAnalyseChangedR = changedByR lcoreSyntaxEq occurAnalyseR

-- | Run GHC's occurrence analyser, and also eliminate any zombies.
occurAnalyseAndDezombifyR :: (AddBindings c, ExtendPath c Crumb, ReadPath c Crumb, HasEmptyContext c, MonadCatch m, Walker c u, Injection CoreExpr u) => Rewrite c m u
occurAnalyseAndDezombifyR = allbuR (tryR $ promoteExprR dezombifyR) >>> occurAnalyseR

occurrenceAnalysisR :: (AddBindings c, ExtendPath c Crumb, ReadPath c Crumb, HasEmptyContext c, MonadCatch m, Walker c LCore) => Rewrite c m LCore
occurrenceAnalysisR = occurAnalyseAndDezombifyR

----------------------------------------------------------------------

-- TODO: this is mostly an example, move somewhere?
buildTypeable :: (HasDynFlags m, HasHermitMEnv m, LiftCoreM m, MonadIO m) => Type -> m (Id, [CoreBind])
buildTypeable ty = do
    evar <- runTcM $ do
        cls <- tcLookupClass typeableClassName
        let predTy = mkClassPred cls [typeKind ty, ty] -- recall that Typeable is now poly-kinded
#if __GLASGOW_HASKELL__ < 710
        newWantedEvVar predTy
#else
        newEvVar predTy
#endif
    buildDictionary evar

-- | Build a dictionary for the given
buildDictionary :: (HasDynFlags m, HasHermitMEnv m, LiftCoreM m, MonadIO m) => Id -> m (Id, [CoreBind])
buildDictionary evar = do
    (i, bs) <- runTcM $ do
#if __GLASGOW_HASKELL__ < 710 || (__GLASGOW_HASKELL__ == 710 && __GLASGOW_HASKELL_PATCHLEVEL1__ <= 2)
        loc <- getCtLoc $ GivenOrigin UnkSkol
#else
        loc <- getCtLocM $ GivenOrigin UnkSkol
#endif
        let predTy = varType evar
            nonC = mkNonCanonical $ CtWanted { ctev_pred = predTy, ctev_evar = evar, ctev_loc = loc }
#if __GLASGOW_HASKELL__ < 710
            wCs = mkFlatWC [nonC]
#elif __GLASGOW_HASKELL__ == 710 && __GLASGOW_HASKELL_PATCHLEVEL1__ <= 2
            wCs = mkSimpleWC [nonC]
#else
            wCs = mkSimpleWC [cc_ev nonC]
#endif
#if __GLASGOW_HASKELL__ < 710 || (__GLASGOW_HASKELL__ == 710 && __GLASGOW_HASKELL_PATCHLEVEL1__ <= 2)
        (_wCs', bnds) <- solveWantedsTcM wCs
#else
        (_wCs', bnds) <- runTcS $ solveWanteds wCs  -- TODO: Make sure this is the right function to call.
#endif
        -- reportAllUnsolved _wCs' -- this is causing a panic with dictionary instantiation
                                  -- revist and fix!
        return (evar, bnds)
    bnds <- runDsM $ dsEvBinds bs
    return (i,bnds)

buildDictionaryT :: (HasDynFlags m, HasHermitMEnv m, LiftCoreM m, MonadCatch m, MonadIO m, MonadUnique m)
                 => Transform c m Type CoreExpr
buildDictionaryT = prefixFailMsg "buildDictionaryT failed: " $ contextfreeT $ \ ty -> do
    dflags <- getDynFlags
    binder <- newIdH ("$d" ++ zEncodeString (filter (not . isSpace) (showPpr dflags ty))) ty
    (i,bnds) <- buildDictionary binder
    guardMsg (notNull bnds) "no dictionary bindings generated."
    return $ case bnds of
                [NonRec v e] | i == v -> e -- the common case that we would have gotten a single non-recursive let
                _ -> mkCoreLets bnds (varToCoreExpr i)

----------------------------------------------------------------------

lintClauseT :: forall c m.
               ( AddBindings c, BoundVars c, ExtendPath c Crumb, HasEmptyContext c, LemmaContext c, ReadPath c Crumb
               , HasDynFlags m, MonadCatch m )
            => Transform c m Clause String
lintClauseT = do
    strs <- extractT (collectPruneT (promoteExprT $ lintExprT `catchM` return) :: Transform c m LCore [String])
    let strs' = nub $ filter notNull strs
    guardMsg (null strs' || (strs' == ["Core Lint Passed"])) $ unlines strs'
    return "Core Lint Passed"

----------------------------------------------------------------------

-- | A LemmaLibrary is a transformation that produces a set of lemmas,
-- which are then added to the lemma store. It is not allowed to insert
-- its own lemmas directly (if it tries they are throw away), but can
-- certainly read the existing store.
type LemmaLibrary = TransformH () Lemmas

loadLemmaLibraryT :: HermitName -> Maybe LemmaName -> TransformH x String
loadLemmaLibraryT nm mblnm = prefixFailMsg "Loading lemma library failed: " $
    contextonlyT $ \ c -> do
        hscEnv <- getHscEnv
        comp <- liftAndCatchIO $ loadLemmaLibrary hscEnv nm
        ls <- applyT comp c () -- TODO: discard side effects
        nls <- maybe (return $ M.toList ls)
                     (\lnm -> maybe (fail $ show lnm ++ " not found in library.")
                                    (\ l -> return [(lnm,l)])
                                    (M.lookup lnm ls))
                     mblnm
        nls' <- flip filterM nls $ \ (n, l) -> do
                    er <- attemptM $ applyT lintClauseT c $ lemmaC l
                    case er of
                        Left msg -> do
                            let pp = Clean.pretty { pOptions = (pOptions Clean.pretty) { po_exprTypes = Detailed } }
                            d <- applyT (liftPrettyH (pOptions pp) $ pLCoreTC pp) c $ inject $ lemmaC l
                            let Glyphs gs = renderCode (pOptions pp) d
                            liftIO $ do
                                putStr "\n" >> sequence_ [ withStyle s t | Glyph t s <- gs ] >> putStr "\n"
                                putStrLn $ "Not adding lemma " ++ show n ++ " because lint failed.\n" ++ msg
                            return False
                        Right _  -> return True
        guardMsg (not (null nls')) "no lemmas to load."
        m <- getLemmas
        putLemmas $ (M.fromList nls') `M.union` m
        return $ "Successfully loaded library " ++ show nm

loadLemmaLibrary :: HscEnv -> HermitName -> IO LemmaLibrary
loadLemmaLibrary hscEnv hnm = do
    name <- lookupHermitNameForPlugins hscEnv varNS hnm
    lib_tycon_name <- lookupHermitNameForPlugins hscEnv tyConClassNS $ fromString "HERMIT.Dictionary.GHC.LemmaLibrary"
    lib_tycon <- forceLoadTyCon hscEnv lib_tycon_name
    mb_v <- getValueSafely hscEnv name $ mkTyConTy lib_tycon
    let dflags = hsc_dflags hscEnv
    maybe (fail $ showSDoc dflags $ hsep
                [ ptext (sLit "The value"), ppr name
                , ptext (sLit "did not have the type")
                , ppr lib_tycon, ptext (sLit "as required.")])
          return mb_v

lookupHermitNameForPlugins :: HscEnv -> NameSpace -> HermitName -> IO Name
lookupHermitNameForPlugins hscEnv ns hnm = do
    modName <- maybe (fail "name must be fully qualified with module name.") return (hnModuleName hnm)
    let dflags = hsc_dflags hscEnv
        rdrName = toRdrName ns hnm
    mbName <- lookupRdrNameInModuleForPlugins hscEnv modName rdrName
    maybe (fail $ showSDoc dflags $ hsep
            [ ptext (sLit "The module"), ppr modName
            , ptext (sLit "did not export the name")
            , ppr rdrName ])
          return mbName

injectDependencyT :: (LiftCoreM m, MonadIO m) => ModuleName -> Transform c m ModGuts ()
injectDependencyT mn = contextfreeT $ \ guts -> do
    env <- getHscEnv
    liftIO $ injectDependency env guts mn
