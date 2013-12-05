{-# LANGUAGE CPP, FlexibleContexts #-}
module HERMIT.Dictionary.Rules
       ( -- * GHC Rewrite Rules and Specialisation
         externals
         -- ** Rules
       , ruleR
       , rulesR
       -- , ruleToEqualityT
       -- , verifyCoreRuleT
       , verifyRuleT
       , ruleLhsIntroR
       , ruleRhsIntroR
         -- ** Specialisation
       , specConstrR
       )
where

import IOEnv hiding (liftIO)
import qualified SpecConstr
import qualified Specialise

import Control.Arrow
import Control.Monad

import Data.Function (on)
import Data.List (deleteFirstsBy,intercalate)

import HERMIT.Core
import HERMIT.Context
import HERMIT.Monad
import HERMIT.Kure
import HERMIT.External
import HERMIT.GHC

import HERMIT.Dictionary.Common (findIdT,inScope)
import HERMIT.Dictionary.GHC (dynFlagsT)
import HERMIT.Dictionary.Induction
import HERMIT.Dictionary.Kure (anyCallR)
import HERMIT.Dictionary.Reasoning hiding (externals)
import HERMIT.Dictionary.Unfold (cleanupUnfoldR)

import qualified Language.Haskell.TH as TH

------------------------------------------------------------------------

-- | Externals that reflect GHC functions, or are derived from GHC functions.
externals :: [External]
externals =
         [ external "rules-help-list" (rulesHelpListT :: TranslateH CoreTC String)
                [ "List all the rules in scope." ] .+ Query
         , external "rule-help" (ruleHelpT :: RuleNameString -> TranslateH CoreTC String)
                [ "Display details on the named rule." ] .+ Query
         , external "apply-rule" (promoteExprR . ruleR :: RuleNameString -> RewriteH Core)
                [ "Apply a named GHC rule" ] .+ Shallow
         , external "apply-rules" (promoteExprR . rulesR :: [RuleNameString] -> RewriteH Core)
                [ "Apply named GHC rules, succeed if any of the rules succeed" ] .+ Shallow
         , external "verify-rule" (verifyRule :: RuleNameString -> RewriteH Core -> RewriteH Core -> TranslateH Core ())
                [ "Verify that the named GHC rule holds (in the current context)." ]
         , external "verify-rule-by-list-induction" (verifyRuleByListInduction  :: RuleNameString -> TH.Name -> RewriteH Core -> RewriteH Core -> RewriteH Core -> RewriteH Core -> TranslateH Core ())
                [ "Verify that the named GHC rule holds, using induction on the named identifier." ] .+ TODO .+ Experiment
         , external "add-rule" ((\ rule_name id_name -> promoteModGutsR (addCoreBindAsRule rule_name id_name)) :: String -> TH.Name -> RewriteH Core)
                [ "add-rule \"rule-name\" <id> -- adds a new rule that freezes the right hand side of the <id>"]  .+ Introduce
         , external "unfold-rule" ((\ nm -> promoteExprR (ruleR nm >>> cleanupUnfoldR)) :: String -> RewriteH Core)
                [ "Unfold a named GHC rule" ] .+ Deep .+ Context .+ TODO -- TODO: does not work with rules with no arguments
         , external "spec-constr" (promoteModGutsR specConstrR :: RewriteH Core)
                [ "Run GHC's SpecConstr pass, which performs call pattern specialization."] .+ Deep
         , external "specialise" (promoteModGutsR specialise :: RewriteH Core)
                [ "Run GHC's specialisation pass, which performs type and dictionary specialisation."] .+ Deep
         , external "rule-unsafe" ((promoteExprBiR . biRuleUnsafeR) :: RuleNameString -> BiRewriteH Core)
                [ "Run a GHC rule forwards or backwards.",
                  "Does not verify that the rule is correct."
                ]
         , external "rule" (biRule :: RuleNameString -> RewriteH Core -> RewriteH Core -> BiRewriteH Core)
                [ "Run a GHC rule forwards or backwards.",
                  "Takes a proof that the rule holds, in the form of a rewrite to apply to both sides to prove the equality."
                ]
         , external "rule-lhs-intro" (ruleLhsIntroR :: RuleNameString -> RewriteH Core)
                [ "Introduce the LHS of a rule as a non-recursive let binding."
                , "body ==> let v = lhs in body" ] .+ Introduce .+ Shallow
         , external "rule-rhs-intro" (ruleRhsIntroR :: RuleNameString -> RewriteH Core)
                [ "Introduce the RHS of a rule as a non-recursive let binding."
                , "body ==> let v = rhs in body" ] .+ Introduce .+ Shallow
         ]

------------------------------------------------------------------------

-- TODO: we have multiple ways of applying RULES as Rewrites now.  We need to clean this up and unify them.

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

-- Neil: Commented this out as it's not (currently) used.
-- rulesToEnv :: [CoreRule] -> Map.Map String (Rewrite c m CoreExpr)
-- rulesToEnv rs = Map.fromList
--         [ ( unpackFS (ruleName r), rulesToRewrite c m [r] )
--         | r <- rs
--         ]

type RuleNameString = String

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

-- | Lookup a rule and attempt to construct a corresponding rewrite.
ruleR :: (ReadBindings c, HasCoreRules c) => RuleNameString -> Rewrite c HermitM CoreExpr
ruleR r = do
    theRules <- getHermitRulesT
    case lookup r theRules of
        Nothing -> fail $ "failed to find rule: " ++ show r
        Just rr -> rulesToRewriteH rr

rulesR :: (ReadBindings c, HasCoreRules c) => [RuleNameString] -> Rewrite c HermitM CoreExpr
rulesR = orR . map ruleR

getHermitRulesT :: HasCoreRules c => Translate c HermitM a [(RuleNameString, [CoreRule])]
getHermitRulesT = contextonlyT $ \ c -> do
    rb     <- liftCoreM getRuleBase
    hscEnv <- liftCoreM getHscEnv
    rb'    <- liftM eps_rule_base $ liftIO $ runIOEnv () $ readMutVar (hsc_EPS hscEnv)
    return [ ( unpackFS (ruleName r), [r] )
           | r <- hermitCoreRules c ++ concat (nameEnvElts rb) ++ concat (nameEnvElts rb')
           ]

getHermitRuleT :: HasCoreRules c => RuleNameString -> Translate c HermitM a [CoreRule]
getHermitRuleT name =
  do rulesEnv <- getHermitRulesT
     case filter ((name ==) . fst) rulesEnv of
       []         -> fail ("Rule \"" ++ name ++ "\" not found.")
       [(_,rus)]  -> return rus
       _          -> fail ("Rule name \"" ++ name ++ "\" is ambiguous.")

getSingletonHermitRuleT :: HasCoreRules c => RuleNameString -> Translate c HermitM a CoreRule
getSingletonHermitRuleT name =
  do rus <- getHermitRuleT name
     case rus of
        []    -> fail "No rules with that name."
        [ru]  -> return ru
        _     -> fail "Multiple rules with that name."


rulesHelpListT :: HasCoreRules c => Translate c HermitM a String
rulesHelpListT = do
    rulesEnv <- getHermitRulesT
    return (intercalate "\n" $ map fst rulesEnv)

ruleHelpT :: HasCoreRules c => RuleNameString -> Translate c HermitM a String
ruleHelpT name = showSDoc <$> dynFlagsT <*> (pprRulesForUser <$> getHermitRuleT name)

-- Too much information.
-- rulesHelpT :: HasCoreRules c => Translate c HermitM a String
-- rulesHelpT = do
--     rulesEnv <- getHermitRulesT
--     dynFlags <- dynFlagsT
--     return  $ (show (map fst rulesEnv) ++ "\n") ++
--               showSDoc dynFlags (pprRulesForUser $ concatMap snd rulesEnv)

makeRule :: RuleNameString -> Id -> CoreExpr -> CoreRule
makeRule rule_name nm =   mkRule True   -- auto-generated
                                 False  -- local
                                 (mkFastString rule_name)
                                 NeverActive    -- because we need to call for these
                                 (varName nm)
                                 []
                                 []

-- TODO: check if a top-level binding
addCoreBindAsRule :: Monad m => RuleNameString -> TH.Name -> Rewrite c m ModGuts
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


-- | Returns the universally quantified binders, the LHS, and the RHS.
ruleToEqualityT :: (BoundVars c, HasGlobalRdrEnv c, HasDynFlags m, MonadThings m, MonadCatch m) => Translate c m CoreRule CoreExprEquality
ruleToEqualityT = withPatFailMsg "HERMIT cannot handle built-in rules yet." $
  do r@Rule{} <- idR -- other possibility is "BuiltinRule"
     f <- findIdT (name2THName $ ru_fn r) -- TODO: I think we're losing information by using name2THName.
                                          -- We need to revise our whole aproach to names and name conversion, to avoid losing info whenever possible.
     return $ CoreExprEquality (ru_bndrs r) (mkCoreApps (Var f) (ru_args r)) (ru_rhs r)

ruleNameToEqualityT :: (BoundVars c, HasGlobalRdrEnv c, HasCoreRules c) => RuleNameString -> Translate c HermitM a CoreExprEquality
ruleNameToEqualityT name = getSingletonHermitRuleT name >>> ruleToEqualityT

verifyRuleT :: (ReadPath c Crumb, Walker c Core, BoundVars c, HasGlobalRdrEnv c, HasCoreRules c)
            => RuleNameString -> CoreExprEqualityProof c HermitM -> Translate c HermitM a ()
verifyRuleT name proof = ruleNameToEqualityT name >>> verifyCoreExprEqualityT proof

verifyRule :: RuleNameString -> RewriteH Core -> RewriteH Core -> TranslateH Core ()
verifyRule name lhsR rhsR = verifyRuleT name (extractR lhsR, extractR rhsR)


--------------------------------------------------------

-- Experimental Test

type BiRewritecHermitMCoreExprShouldGoHere = ()

verifyRuleByListInductionT :: (AddBindings c, ReadBindings c, ReadPath c Crumb, ExtendPath c Crumb, Walker c Core, BoundVars c, HasGlobalRdrEnv c, HasCoreRules c)
            => RuleNameString -> TH.Name -> CoreExprEqualityProof c HermitM -> (BiRewritecHermitMCoreExprShouldGoHere -> CoreExprEqualityProof c HermitM) -> Translate c HermitM a ()
verifyRuleByListInductionT r_name i_name nilCaseProof consCaseProof = ruleNameToEqualityT r_name >>> listInductionOnT (cmpTHName2Var i_name) nilCaseProof (\ _ -> consCaseProof ())

verifyRuleByListInduction  :: RuleNameString    -- Name of Rule to prove
                           -> TH.Name           -- Name if Id to perform induction on
                           -> RewriteH Core     -- [] case, LHS
                           -> RewriteH Core     -- [] case, RHS
                           -> RewriteH Core     -- (:) case, LHS
                           -> RewriteH Core     -- (:) case, RHS
                           -> TranslateH Core ()
verifyRuleByListInduction r_name i_name nilLhsR nilRhsR consLhsR consRhsR = verifyRuleByListInductionT r_name i_name (extractR nilLhsR, extractR nilRhsR) (\ () -> (extractR consLhsR, extractR consRhsR))

--------------------------------------------------------


biRuleUnsafeR ::
           ( BoundVars c
           , HasCoreRules c
           , HasGlobalRdrEnv c
           , AddBindings c
           , ReadBindings c
           , ExtendPath c Crumb
           , ReadPath c Crumb)
        => RuleNameString -> BiRewrite c HermitM CoreExpr
biRuleUnsafeR name = beforeBiR (ruleNameToEqualityT name) birewrite

biRuleR :: ( BoundVars c
           , HasCoreRules c
           , HasGlobalRdrEnv c
           , AddBindings c
           , ReadBindings c
           , ExtendPath c Crumb
           , ReadPath c Crumb)
        => RuleNameString -> CoreExprEqualityProof c HermitM -> BiRewrite c HermitM CoreExpr
biRuleR name proof = beforeBiR
                            (do eq <- ruleNameToEqualityT name
                                verifyCoreExprEqualityT proof <<< return eq
                                return eq
                            )
                            birewrite

biRule :: RuleNameString -> RewriteH Core -> RewriteH Core -> BiRewriteH Core
biRule name lhsR rhsR = promoteExprBiR $ biRuleR name (extractR lhsR, extractR rhsR)

------------------------------------------------------------------------

-- | @e@ ==> @let v = lhs in e@  (also works in a similar manner at Program nodes)
ruleLhsIntroR :: (BoundVars c, HasGlobalRdrEnv c, HasCoreRules c) => RuleNameString -> Rewrite c HermitM Core
ruleLhsIntroR = ruleNameToEqualityT >=> eqLhsIntroR

-- | @e@ ==> @let v = rhs in e@  (also works in a similar manner at Program nodes)
ruleRhsIntroR :: (BoundVars c, HasGlobalRdrEnv c, HasCoreRules c) => RuleNameString -> Rewrite c HermitM Core
ruleRhsIntroR = ruleNameToEqualityT >=> eqRhsIntroR

------------------------------------------------------------------------

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
bindSpecRules =    recT (\_ -> defT idSpecRules successT const) concat
                <+ nonRecT idSpecRules successT const

-- | Find all specialization rules in a Core fragment.
specRules :: TranslateH Core [CoreRule]
specRules = crushtdT $ promoteBindT bindSpecRules

------------------------------------------------------------------------
