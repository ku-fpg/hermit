{-# LANGUAGE CPP, FlexibleContexts #-}
module HERMIT.Dictionary.Rules
       ( -- * GHC Rewrite Rules and Specialisation
         externals
         -- ** Rules
       , RuleNameString
       , ruleR
       , rulesR
       , ruleToEqualityT
       , ruleNameToEqualityT
       , getHermitRuleT
       , getHermitRulesT
       -- , verifyCoreRuleT
       -- , verifyRuleT
       -- , ruleLhsIntroR
       -- , ruleRhsIntroR
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

import HERMIT.Dictionary.Common (inScope,callT)
import HERMIT.Dictionary.GHC (dynFlagsT)
import HERMIT.Dictionary.Kure (anyCallR)
import HERMIT.Dictionary.Unfold (cleanupUnfoldR)

------------------------------------------------------------------------

-- | Externals that reflect GHC functions, or are derived from GHC functions.
externals :: [External]
externals =
         [ external "rules-help-list" (rulesHelpListT :: TransformH CoreTC String)
                [ "List all the rules in scope." ] .+ Query
         , external "rule-help" (ruleHelpT :: RuleNameString -> TransformH CoreTC String)
                [ "Display details on the named rule." ] .+ Query
         , external "apply-rule" (promoteExprR . ruleR :: RuleNameString -> RewriteH Core)
                [ "Apply a named GHC rule" ] .+ Shallow
         , external "apply-rules" (promoteExprR . rulesR :: [RuleNameString] -> RewriteH Core)
                [ "Apply named GHC rules, succeed if any of the rules succeed" ] .+ Shallow
         , external "add-rule" ((\ rule_name id_name -> promoteModGutsR (addCoreBindAsRule rule_name id_name)) :: String -> String -> RewriteH Core)
                [ "add-rule \"rule-name\" <id> -- adds a new rule that freezes the right hand side of the <id>"]  .+ Introduce
         , external "unfold-rule" ((\ nm -> promoteExprR (ruleR nm >>> cleanupUnfoldR)) :: String -> RewriteH Core)
                [ "Unfold a named GHC rule" ] .+ Deep .+ Context .+ TODO -- TODO: does not work with rules with no arguments
         , external "spec-constr" (promoteModGutsR specConstrR :: RewriteH Core)
                [ "Run GHC's SpecConstr pass, which performs call pattern specialization."] .+ Deep
         , external "specialise" (promoteModGutsR specialise :: RewriteH Core)
                [ "Run GHC's specialisation pass, which performs type and dictionary specialisation."] .+ Deep
         ]

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

-- Neil: Commented this out as it's not (currently) used.
-- rulesToEnv :: [CoreRule] -> Map.Map String (Rewrite c m CoreExpr)
-- rulesToEnv rs = Map.fromList
--         [ ( unpackFS (ruleName r), rulesToRewrite c m [r] )
--         | r <- rs
--         ]

type RuleNameString = String

-- TODO: deprecate this (and related functions) in favor of 'biRuleUnsafeR'
#if __GLASGOW_HASKELL__ > 706
rulesToRewriteH :: (ReadBindings c, HasDynFlags m, MonadCatch m) => [CoreRule] -> Rewrite c m CoreExpr
#else
rulesToRewriteH :: (ReadBindings c, MonadCatch m) => [CoreRule] -> Rewrite c m CoreExpr
#endif
rulesToRewriteH rs = prefixFailMsg "RulesToRewrite failed: " $
                     withPatFailMsg "rule not matched." $ do
    (Var fn, args) <- callT
    transform $ \ c e -> do
        let in_scope = mkInScopeSet (mkVarEnv [ (v,v) | v <- varSetElems (localFreeVarsExpr e) ])
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
        Nothing -> fail $ "failed to find rule: " ++ show r ++ ". If you think the rule exists, try running the flatten-module command at the top level."
        Just rr -> rulesToRewriteH [rr]

rulesR :: (ReadBindings c, HasCoreRules c) => [RuleNameString] -> Rewrite c HermitM CoreExpr
rulesR = orR . map ruleR

-- | Return all the RULES (including specialization RULES on binders) currently in scope.
getHermitRulesT :: HasCoreRules c => Transform c HermitM a [(RuleNameString, CoreRule)]
getHermitRulesT = contextonlyT $ \ c -> do
    rb      <- liftCoreM getRuleBase
    mgRules <- liftM mg_rules getModGuts
    hscEnv  <- liftCoreM getHscEnv
    rb'     <- liftM eps_rule_base $ liftIO $ runIOEnv () $ readMutVar (hsc_EPS hscEnv)
    return [ (unpackFS (ruleName r), r)
           | r <- hermitCoreRules c ++ mgRules ++ concat (nameEnvElts rb) ++ concat (nameEnvElts rb')
           ]

getHermitRuleT :: HasCoreRules c => RuleNameString -> Transform c HermitM a CoreRule
getHermitRuleT name =
  do rulesEnv <- getHermitRulesT
     case filter ((name ==) . fst) rulesEnv of
       []      -> fail ("Rule \"" ++ name ++ "\" not found.")
       [(_,r)] -> return r
       _       -> fail ("Rule name \"" ++ name ++ "\" is ambiguous.")

rulesHelpListT :: HasCoreRules c => Transform c HermitM a String
rulesHelpListT = do
    rulesEnv <- getHermitRulesT
    return (intercalate "\n" $ reverse $ map fst rulesEnv)

ruleHelpT :: HasCoreRules c => RuleNameString -> Transform c HermitM a String
ruleHelpT name = showSDoc <$> dynFlagsT <*> ((pprRulesForUser . (:[])) <$> getHermitRuleT name)

-- Too much information.
-- rulesHelpT :: HasCoreRules c => Transform c HermitM a String
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
addCoreBindAsRule :: Monad m => RuleNameString -> String -> Rewrite c m ModGuts
addCoreBindAsRule rule_name nm = contextfreeT $ \ modGuts ->
        case [ (v,e)
             | bnd   <- mg_binds modGuts
             , (v,e) <- bindToVarExprs bnd
             ,  nm `cmpString2Var` v
             ] of
         [] -> fail $ "cannot find binding " ++ nm
         [(v,e)] -> return $ modGuts { mg_rules = mg_rules modGuts
                                              ++ [makeRule rule_name v e]
                                     }
         _ -> fail $ "found multiple bindings for " ++ nm

-- | Returns the universally quantified binders, the LHS, and the RHS.
ruleToEqualityT :: (BoundVars c, HasDynFlags m, HasModGuts m, MonadThings m, MonadCatch m) => Transform c m CoreRule CoreExprEquality
ruleToEqualityT = withPatFailMsg "HERMIT cannot handle built-in rules yet." $
  do r@Rule{} <- idR -- other possibility is "BuiltinRule"
     f <- lookupId $ ru_fn r
     return $ CoreExprEquality (ru_bndrs r) (mkCoreApps (Var f) (ru_args r)) (ru_rhs r)

ruleNameToEqualityT :: (BoundVars c, HasCoreRules c) => RuleNameString -> Transform c HermitM a CoreExprEquality
ruleNameToEqualityT name = getHermitRuleT name >>> ruleToEqualityT

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

#if __GLASGOW_HASKELL__ <= 706
    dflags <- dynFlagsT
    guts <- contextfreeT $ liftCoreM . Specialise.specProgram dflags
#else
    guts <- contextfreeT $ liftCoreM . Specialise.specProgram
#endif

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
idSpecRules :: TransformH Id [CoreRule]
idSpecRules = do
    guardMsgM (arr isId) "idSpecRules called on TyVar." -- idInfo panics on TyVars
    contextfreeT $ \ i -> let SpecInfo rs _ = specInfo (idInfo i) in return rs

-- | Promote 'idSpecRules' to CoreBind.
bindSpecRules :: TransformH CoreBind [CoreRule]
bindSpecRules =    recT (\_ -> defT idSpecRules successT const) concat
                <+ nonRecT idSpecRules successT const

-- | Find all specialization rules in a Core fragment.
specRules :: TransformH Core [CoreRule]
specRules = crushtdT $ promoteBindT bindSpecRules

------------------------------------------------------------------------
