{-# LANGUAGE CPP, FlexibleContexts, ScopedTypeVariables #-}
module HERMIT.Dictionary.GHC
       ( -- * GHC-based Transformations
         -- | This module contains transformations that are reflections of GHC functions, or derived from GHC functions.
         externals
       , anyCallR
         -- ** Substitution
       , substR
       , substExprR
         -- ** Utilities
       , inScope
       , rule
       , rules
       , dynFlagsT
       , arityOf
         -- ** Lifted GHC capabilities
         -- A zombie is an identifer that has 'OccInfo' 'IAmDead', but still has occurrences.
       , lintExprT
       , lintModuleT
       , specConstrR
       , occurAnalyseR
       , occurAnalyseChangedR
       , occurAnalyseExprChangedR
       , occurAnalyseAndDezombifyR
       , dezombifyR
       )
where

import qualified Bag
import qualified CoreLint
import IOEnv hiding (liftIO)
import qualified SpecConstr
import qualified Specialise

import Control.Arrow
import Control.Monad

import Data.Function (on)
import Data.List (mapAccumL,deleteFirstsBy)

import HERMIT.Core
import HERMIT.Context
import HERMIT.Monad
import HERMIT.Kure
import HERMIT.External
import HERMIT.GHC

import HERMIT.Dictionary.Debug hiding (externals)
import HERMIT.Dictionary.Kure (unitT)

import qualified Language.Haskell.TH as TH

------------------------------------------------------------------------

-- | Externals that reflect GHC functions, or are derived from GHC functions.
externals :: [External]
externals =
         [ external "deshadow-prog" (promoteProgR deShadowProgR :: RewriteH Core)
                [ "Deshadow a program." ] .+ Deep
         , external "apply-rule" (promoteExprR . rule :: String -> RewriteH Core)
                [ "Apply a named GHC rule" ] .+ Shallow
         , external "apply-rule" (rules_help :: TranslateH Core String)
                [ "List rules that can be used" ] .+ Query
         , external "apply-rules" (promoteExprR . rules :: [String] -> RewriteH Core)
                [ "Apply named GHC rules, succeed if any of the rules succeed" ] .+ Shallow
         , external "add-rule" ((\ rule_name id_name -> promoteModGutsR (addCoreBindAsRule rule_name id_name)) :: String -> TH.Name -> RewriteH Core)
                [ "add-rule \"rule-name\" <id> -- adds a new rule that freezes the right hand side of the <id>"]  .+ Introduce
         , external "dezombify" (promoteExprR dezombifyR :: RewriteH Core)
                [ "Zap the occurrence information in the current identifer if it is a zombie."] .+ Shallow
         , external "occurrence-analysis" (occurrenceAnalysisR :: RewriteH Core)
                [ "Perform dependency analysis on all sub-expressions; simplifying and updating identifer info."] .+ Deep
         , external "lint-expr" (promoteExprT lintExprT :: TranslateH Core String)
                [ "Runs GHC's Core Lint, which typechecks the current expression."
                , "Note: this can miss several things that a whole-module core lint will find."
                , "For instance, running this on the RHS of a binding, the type of the RHS will"
                , "not be checked against the type of the binding. Running on the whole let expression"
                , "will catch that however."] .+ Deep .+ Debug .+ Query
         , external "lint-module" (promoteModGutsT lintModuleT :: TranslateH Core String)
                [ "Runs GHC's Core Lint, which typechecks the current module."] .+ Deep .+ Debug .+ Query
         , external "spec-constr" (promoteModGutsR specConstrR :: RewriteH Core)
                [ "Run GHC's SpecConstr pass, which performs call pattern specialization."] .+ Deep
         , external "specialise" (promoteModGutsR specialise :: RewriteH Core)
                [ "Run GHC's specialisation pass, which performs type and dictionary specialization."] .+ Deep
         , external "any-call" (anyCallR :: RewriteH Core -> RewriteH Core)
                [ "any-call (.. unfold command ..) applies an unfold command to all applications."
                , "Preference is given to applications with more arguments." ] .+ Deep
         ]

------------------------------------------------------------------------

-- | Substitute all occurrences of a variable with an expression, in either a program or an expression.
substR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, MonadCatch m) => Var -> CoreExpr -> Rewrite c m Core
substR v e = setFailMsg "Can only perform substitution on expressions or programs." $
             promoteExprR (substExprR v e) <+ promoteProgR (substTopBindR v e) <+ promoteAltR (substAltR v e)

-- | Substitute all occurrences of a variable with an expression, in an expression.
substExprR :: Monad m => Var -> CoreExpr -> Rewrite c m CoreExpr
substExprR v e =  contextfreeT $ \ expr -> do
    -- The InScopeSet needs to include any free variables appearing in the
    -- expression to be substituted.  Constructing a NonRec Let expression
    -- to pass on to exprFeeVars takes care of this, but ...
    -- TODO Is there a better way to do this ???
    let emptySub = mkEmptySubst (mkInScopeSet (localFreeVarsExpr (Let (NonRec v e) expr)))
    return $ substExpr (text "substR") (extendSubst emptySub v e) expr

-- | Substitute all occurrences of a variable with an expression, in a program.
substTopBindR :: Monad m => Var -> CoreExpr -> Rewrite c m CoreProg
substTopBindR v e =  contextfreeT $ \ p -> do
    -- TODO.  Do we need to initialize the emptySubst with bindFreeVars?
    let emptySub =  emptySubst -- mkEmptySubst (mkInScopeSet (exprFreeVars exp))
    return $ bindsToProg $ snd (mapAccumL substBind (extendSubst emptySub v e) (progToBinds p))

-- | Substitute all occurrences of a variable with an expression, in a case alternative.
substAltR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, Monad m) => Var -> CoreExpr -> Rewrite c m CoreAlt
substAltR v e = do (_, vs, _) <- idR
                   if v `elem` vs
                    then fail "variable is shadowed by a case-alternative constructor argument."
                    else altAllR idR (\ _ -> idR) (substExprR v e)

-- Neil: Commented this out as it's not (currently) used.
--  Perform let-substitution the specified number of times.
-- letSubstNR :: Int -> Rewrite c m Core
-- letSubstNR 0 = idR
-- letSubstNR n = childR 1 (letSubstNR (n - 1)) >>> promoteExprR letSubstR

------------------------------------------------------------------------

-- | [from GHC documentation] De-shadowing the program is sometimes a useful pre-pass.
-- It can be done simply by running over the bindings with an empty substitution,
-- becuase substitution returns a result that has no-shadowing guaranteed.
--
-- (Actually, within a single /type/ there might still be shadowing, because
-- 'substTy' is a no-op for the empty substitution, but that's probably OK.)
deShadowProgR :: Monad m => Rewrite c m CoreProg
deShadowProgR = arr (bindsToProg . deShadowBinds . progToBinds)

------------------------------------------------------------------------
{-
lookupRule :: (Activation -> Bool)	-- When rule is active
	    -> IdUnfoldingFun		-- When Id can be unfolded
            -> InScopeSet
	    -> Id -> [CoreExpr]
	    -> [CoreRule] -> Maybe (CoreRule, CoreExpr)

GHC HEAD:
type InScopeEnv = (InScopeSet, IdUnfoldingFun)

lookupRule :: DynFlags -> InScopeEnv
           -> (Activation -> Bool)      -- When rule is active
           -> Id -> [CoreExpr]
           -> [CoreRule] -> Maybe (CoreRule, CoreExpr)
-}

-- Neil: Commented this out as its not (currently) used.
-- rulesToEnv :: [CoreRule] -> Map.Map String (Rewrite c m CoreExpr)
-- rulesToEnv rs = Map.fromList
--         [ ( unpackFS (ruleName r), rulesToRewrite c m [r] )
--         | r <- rs
--         ]

#if __GLASGOW_HASKELL__ > 706
rulesToRewriteH :: (ReadBindings c, HasDynFlags m, MonadCatch m) => [CoreRule] -> Rewrite c m CoreExpr
#else
rulesToRewriteH :: (ReadBindings c, MonadCatch m) => [CoreRule] -> Rewrite c m CoreExpr
#endif
rulesToRewriteH rs = prefixFailMsg "RulesToRewrite failed: " $
                     withPatFailMsg "rule not matched." $
                     translate $ \ c e -> do
    -- First, we normalize the lhs, so we can match it
    (Var fn,args) <- return $ collectArgs e
    -- Question: does this include Id's, or Var's (which include type names)
    -- Assumption: Var's.
    let in_scope = mkInScopeSet (mkVarEnv [ (v,v) | v <- varSetElems (localFreeVarsExpr e) ])
        -- The rough_args are just an attempt to try eliminate silly things
        -- that will never match
        _rough_args = map (const Nothing) args   -- rough_args are never used!!! FIX ME!
    -- Finally, we try match the rules
    -- trace (showSDoc (ppr fn <+> ppr args $$ ppr rs)) $
#if __GLASGOW_HASKELL__ > 706
    dflags <- getDynFlags
    case lookupRule dflags (in_scope, const NoUnfolding) (const True) fn args [r | r <- rs, ru_fn r == idName fn] of
#else
    case lookupRule (const True) (const NoUnfolding) in_scope fn args [r | r <- rs, ru_fn r == idName fn] of
#endif
        Nothing         -> fail "rule not matched"
        Just (r, expr)  -> do
            let e' = mkApps expr (drop (ruleArity r) args)
            if all (inScope c) $ varSetElems $ localFreeVarsExpr e' -- TODO: The problem with this check, is that it precludes the case where this is an intermediate transformation.  I can imagine situations where some variables would be out-of-scope at this point, but in scope again after a subsequent transformation.
              then return e'
              else fail $ unlines ["Resulting expression after rule application contains variables that are not in scope."
                                  ,"This can probably be solved by running the flatten-module command at the top level."]

-- | Determine whether an identifier is in scope.
inScope :: ReadBindings c => c -> Id -> Bool
inScope c v = (v `boundIn` c) ||                 -- defined in this module
              case unfoldingInfo (idInfo v) of
                CoreUnfolding {} -> True         -- defined elsewhere
                DFunUnfolding {} -> True
                _                -> False

-- | Lookup a rule and attempt to construct a corresponding rewrite.
rule :: (ReadBindings c, HasCoreRules c) => String -> Rewrite c HermitM CoreExpr
rule r = do
    theRules <- getHermitRules
    case lookup r theRules of
        Nothing -> fail $ "failed to find rule: " ++ show r
        Just rr -> rulesToRewriteH rr

rules :: (ReadBindings c, HasCoreRules c) => [String] -> Rewrite c HermitM CoreExpr
rules = orR . map rule

getHermitRules :: HasCoreRules c => Translate c HermitM a [(String, [CoreRule])]
getHermitRules = contextonlyT $ \ c -> do
    rb     <- liftCoreM getRuleBase
    hscEnv <- liftCoreM getHscEnv
    rb'    <- liftM eps_rule_base $ liftIO $ runIOEnv () $ readMutVar (hsc_EPS hscEnv)
    return [ ( unpackFS (ruleName r), [r] )
           | r <- hermitCoreRules c ++ concat (nameEnvElts rb) ++ concat (nameEnvElts rb')
           ]

rules_help :: HasCoreRules c => Translate c HermitM Core String
rules_help = do
    rulesEnv <- getHermitRules
    dynFlags <- dynFlagsT
    return  $ (show (map fst rulesEnv) ++ "\n") ++
              showSDoc dynFlags (pprRulesForUser $ concatMap snd rulesEnv)

makeRule :: String -> Id -> CoreExpr -> CoreRule
makeRule rule_name nm =   mkRule True   -- auto-generated
                                 False  -- local
                                 (mkFastString rule_name)
                                 NeverActive    -- because we need to call for these
                                 (varName nm)
                                 []
                                 []

-- TODO: check if a top-level binding
addCoreBindAsRule :: Monad m => String -> TH.Name -> Rewrite c m ModGuts
addCoreBindAsRule rule_name nm = contextfreeT $ \ modGuts ->
        case [ (v,e)
             | bnd   <- mg_binds modGuts
             , (v,e) <- bindToVarExprs bnd
             ,  nm `cmpTHName2Var` v
             ] of
         [] -> fail $ "cannot find binding " ++ show nm
         [(v,e)] -> return $ modGuts { mg_rules = mg_rules modGuts
                                              ++ [makeRule rule_name v e]
                                     }
         _ -> fail $ "found multiple bindings for " ++ show nm

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
lintModuleT :: TranslateH ModGuts String
lintModuleT =
  do dynFlags <- dynFlagsT
     bnds     <- arr mg_binds
#if __GLASGOW_HASKELL__ > 706
     let (warns, errs)    = CoreLint.lintCoreBindings [] bnds -- [] are vars to treat as in scope, used by GHCi
#else
     let (warns, errs)    = CoreLint.lintCoreBindings bnds
#endif
         dumpSDocs endMsg = Bag.foldBag (\ d r -> d ++ ('\n':r)) (showSDoc dynFlags) endMsg
     if Bag.isEmptyBag errs
       then return $ dumpSDocs "Core Lint Passed" warns
       else observeR (dumpSDocs "" errs) >>> fail "Core Lint Failed"

-- | Note: this can miss several things that a whole-module core lint will find.
-- For instance, running this on the RHS of a binding, the type of the RHS will
-- not be checked against the type of the binding. Running on the whole let expression
-- will catch that however.
lintExprT :: (BoundVars c, Monad m, HasDynFlags m) => Translate c m CoreExpr String
lintExprT = translate $ \ c e -> do
    dflags <- getDynFlags
    maybe (return "Core Lint Passed") (fail . showSDoc dflags)
#if __GLASGOW_HASKELL__ > 706
                 $ CoreLint.lintExpr (varSetElems $ boundVars c) e
#else
                 $ CoreLint.lintUnfolding noSrcLoc (varSetElems $ boundVars c) e
#endif

-- | Run GHC's specConstr pass, and apply any rules generated.
specConstrR :: RewriteH ModGuts
specConstrR = prefixFailMsg "spec-constr failed: " $ do
    rs  <- extractT specRules
    e'  <- contextfreeT $ liftCoreM . SpecConstr.specConstrProgram
    rs' <- return e' >>> extractT specRules
    let specRs = deleteFirstsBy ((==) `on` ru_name) rs' rs
    guardMsg (notNull specRs) "no rules created."
    return e' >>> extractR (repeatR (anyCallR (promoteExprR $ rulesToRewriteH specRs)))

-- | Run GHC's specialisation pass, and apply any rules generated.
specialise :: RewriteH ModGuts
specialise = prefixFailMsg "specialisation failed: " $ do
    gRules <- arr mg_rules
    lRules <- extractT specRules

    dflags <- dynFlagsT
    guts <- contextfreeT $ liftCoreM . Specialise.specProgram dflags

    lRules' <- return guts >>> extractT specRules -- spec rules on bindings in this module
    let gRules' = mg_rules guts            -- plus spec rules on imported bindings
        gSpecRs = deleteFirstsBy ((==) `on` ru_name) gRules' gRules
        lSpecRs = deleteFirstsBy ((==) `on` ru_name) lRules' lRules
        specRs = gSpecRs ++ lSpecRs
    guardMsg (notNull specRs) "no rules created."
    liftIO $ putStrLn $ unlines $ map (unpackFS . ru_name) specRs
    return guts >>> extractR (repeatR (anyCallR (promoteExprR $ rulesToRewriteH specRs)))

-- | Get all the specialization rules on a binding.
--   These are created by SpecConstr and other GHC passes.
idSpecRules :: TranslateH Id [CoreRule]
idSpecRules = contextfreeT $ \ i -> let SpecInfo rs _ = specInfo (idInfo i) in return rs

-- | Promote 'idSpecRules' to CoreBind.
bindSpecRules :: TranslateH CoreBind [CoreRule]
bindSpecRules =    recT (\_ -> defT idSpecRules unitT const) concat
                <+ nonRecT idSpecRules unitT const

-- | Find all specialization rules in a Core fragment.
specRules :: TranslateH Core [CoreRule]
specRules = crushtdT $ promoteBindT bindSpecRules

-- | Top-down traversal tuned to matching function calls.
anyCallR :: forall c m. (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, MonadCatch m)
         => Rewrite c m Core -> Rewrite c m Core
anyCallR rr = prefixFailMsg "any-call failed: " $
              readerT $ \ e -> case e of
        ExprCore (App {}) -> childR App_Arg rec >+> (rr <+ childR App_Fun rec)
        ExprCore (Var {}) -> rr
        _                 -> anyR rec
    where rec :: Rewrite c m Core
          rec = anyCallR rr

-------------------------------------------

-- | Lifted version of 'getDynFlags'.
dynFlagsT :: HasDynFlags m => Translate c m a DynFlags
dynFlagsT = constT getDynFlags

-------------------------------------------

----------------------------------------------------------------------

-- TODO: Ideally, occurAnalyseExprR would fail if nothing changed.
--       This is tricky though, as it's not just the structure of the expression, but also the meta-data.

-- | Zap the 'OccInfo' in a zombie identifier.
dezombifyR :: (ExtendPath c Crumb, Monad m) => Rewrite c m CoreExpr
dezombifyR = varR (acceptR isDeadBinder >>^ zapVarOccInfo)

-- | Apply 'occurAnalyseExprR' to all sub-expressions.
occurAnalyseR :: (AddBindings c, ExtendPath c Crumb, ReadPath c Crumb, MonadCatch m) => Rewrite c m Core
occurAnalyseR = let r  = promoteExprR (arr occurAnalyseExpr)
                    go = r <+ anyR go
                 in tryR go -- always succeed

-- | Occurrence analyse an expression, failing if the result is syntactically equal to the initial expression.
occurAnalyseExprChangedR :: MonadCatch m => Rewrite c m CoreExpr
occurAnalyseExprChangedR = changedByR exprSyntaxEq (arr occurAnalyseExpr)

-- | Occurrence analyse all sub-expressions, failing if the result is syntactically equal to the initial expression.
occurAnalyseChangedR :: (AddBindings c, ExtendPath c Crumb, ReadPath c Crumb, MonadCatch m) => Rewrite c m Core
occurAnalyseChangedR = changedByR coreSyntaxEq occurAnalyseR

-- | Run GHC's occurrence analyser, and also eliminate any zombies.
occurAnalyseAndDezombifyR :: (AddBindings c, ExtendPath c Crumb, ReadPath c Crumb, MonadCatch m) => Rewrite c m Core
occurAnalyseAndDezombifyR = allbuR (tryR $ promoteExprR dezombifyR) >>> occurAnalyseR

occurrenceAnalysisR :: (AddBindings c, ExtendPath c Crumb, ReadPath c Crumb, MonadCatch m) => Rewrite c m Core
occurrenceAnalysisR = occurAnalyseAndDezombifyR

{- Does not work (no export)
-- Here is a hook into the occur analysis, and a way of looking at the result
occAnalysis ::  CoreExpr -> UsageDetails
occAnalysis = fst . occAnal (initOccEnv all_active_rules)

lookupUsageDetails :: UsageDetails -> Var -> Maybe OccInfo
lookupUsageDetails = lookupVarEnv

-}

----------------------------------------------------------------------
