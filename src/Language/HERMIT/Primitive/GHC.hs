{-# LANGUAGE CPP #-}
module Language.HERMIT.Primitive.GHC
       ( -- * GHC-based Transformations
         -- | This module contains transformations that are reflections of GHC functions, or derived from GHC functions.
         externals
         -- ** Free Variables
       , coreExprFreeIds
       , coreExprFreeVars
       , freeIdsT
       , freeVarsT
       , altFreeVarsT
       , altFreeVarsExclWildT
         -- ** Substitution
       , substR
       , substExprR
       , letSubstR
       , safeLetSubstR
       , safeLetSubstPlusR
         -- ** Equality
       , exprEqual
       , exprsEqual
       , coreEqual
         -- ** Utilities
       , inScope
       , showVars
       , rule
       , rules
       , lintExprT
       , lintProgramT
       , lintModuleT
       , equivalent
       )
where

import GhcPlugins
import qualified Bag
import qualified CoreLint
import qualified OccurAnal
import IOEnv

import Control.Arrow
import Control.Monad
import Data.List (intercalate,mapAccumL,(\\))
import Data.Map (keys)

import Language.HERMIT.Core
import Language.HERMIT.Context
import Language.HERMIT.Monad
import Language.HERMIT.Kure
import Language.HERMIT.External
import Language.HERMIT.GHC

import Language.HERMIT.Primitive.Debug hiding (externals)
import Language.HERMIT.Primitive.Navigation hiding (externals)

import qualified Language.Haskell.TH as TH

------------------------------------------------------------------------

-- | Externals that reflect GHC functions, or are derived from GHC functions.
externals :: [External]
externals =
         [ external "info" (info :: TranslateH Core String)
                [ "display information about the current node." ]
         , external "let-subst" (promoteExprR letSubstR :: RewriteH Core)
                [ "Let substitution"
                , "(let x = e1 in e2) ==> (e2[e1/x])"
                , "x must not be free in e1." ]                           .+ Deep
         , external "safe-let-subst" (promoteExprR safeLetSubstR :: RewriteH Core)
                [ "Safe let substitution"
                , "let x = e1 in e2, safe to inline without duplicating work ==> e2[e1/x],"
                , "x must not be free in e1." ]                           .+ Deep .+ Eval .+ Bash
         , external "safe-let-subst-plus" (promoteExprR safeLetSubstPlusR :: RewriteH Core)
                [ "Safe let substitution"
                , "let { x = e1, ... } in e2, "
                , "  where safe to inline without duplicating work ==> e2[e1/x,...],"
                , "only matches non-recursive lets" ]  .+ Deep .+ Eval
         , external "free-ids" (promoteExprT freeIdsQuery :: TranslateH Core String)
                [ "List the free identifiers in this expression." ] .+ Query .+ Deep
         , external "deshadow-prog" (promoteProgR deShadowProgR :: RewriteH Core)
                [ "Deshadow a program." ] .+ Deep
         , external "apply-rule" (promoteExprR . rule :: String -> RewriteH Core)
                [ "apply a named GHC rule" ] .+ Shallow
         , external "apply-rule" (rules_help :: TranslateH Core String)
                [ "list rules that can be used" ] .+ Query
         , external "apply-rules" (promoteExprR . rules :: [String] -> RewriteH Core)
                [ "apply named GHC rules, succeeds if any of the rules succeed" ] .+ Shallow
         , external "compare-values" compareValues
                ["compare the rhs of two values."] .+ Query .+ Predicate
         , external "add-rule" (\ rule_name id_name -> promoteModGutsR (addCoreBindAsRule rule_name id_name))
                ["add-rule \"rule-name\" <id> -- adds a new rule that freezes the right hand side of the <id>"]
                                        .+ Introduce
         , external "occur-analysis" (promoteExprR occurAnalyseExprR :: RewriteH Core)
                ["Performs dependency anlaysis on a CoreExpr.",
                 "This can be useful to simplify a recursive let to a non-recursive let."] .+ Deep
         , external "lintExpr" (promoteExprT lintExprT :: TranslateH Core String)
                ["Runs GHC's Core Lint, which typechecks the current expression."
                ,"Note: this can miss several things that a whole-module core lint will find."
                ,"For instance, running this on the RHS of a binding, the type of the RHS will"
                ,"not be checked against the type of the binding. Running on the whole let expression"
                ,"will catch that however."] .+ Deep .+ Debug .+ Query
         , external "lintProg" (promoteProgT lintProgramT :: TranslateH Core String)
                ["Runs GHC's Core Lint, which typechecks the top level list of bindings."] .+ Deep .+ Debug .+ Query
         , external "lintModule" (promoteModGutsT lintModuleT :: TranslateH Core String)
                ["Runs GHC's Core Lint, which typechecks the current module."] .+ Deep .+ Debug .+ Query
         ]

------------------------------------------------------------------------

-- | Substitute all occurrences of a variable with an expression, in either a program or an expression.
substR :: Var -> CoreExpr -> RewriteH Core
substR v e = setFailMsg "Can only perform substitution on expressions or programs." $
             promoteExprR (substExprR v e) <+ promoteProgR (substTopBindR v e) <+ promoteAltR (substAltR v e)

-- | Substitute all occurrences of a variable with an expression, in an expression.
substExprR :: Var -> CoreExpr -> RewriteH CoreExpr
substExprR v e =  contextfreeT $ \ expr -> do
    -- The InScopeSet needs to include any free variables appearing in the
    -- expression to be substituted.  Constructing a NonRec Let expression
    -- to pass on to exprFeeVars takes care of this, but ...
    -- TODO Is there a better way to do this ???
    let emptySub = mkEmptySubst (mkInScopeSet (exprFreeVars (Let (NonRec v e) expr)))
    return $ substExpr (text "substR") (extendSubst emptySub v e) expr

-- | Substitute all occurrences of a variable with an expression, in a program.
substTopBindR :: Var -> CoreExpr -> RewriteH CoreProg
substTopBindR v e =  contextfreeT $ \ p -> do
    -- TODO.  Do we need to initialize the emptySubst with bindFreeVars?
    let emptySub =  emptySubst -- mkEmptySubst (mkInScopeSet (exprFreeVars exp))
    return $ bindsToProg $ snd (mapAccumL substBind (extendSubst emptySub v e) (progToBinds p))

-- | Substitute all occurrences of a variable with an expression, in a case alternative.
substAltR :: Var -> CoreExpr -> RewriteH CoreAlt
substAltR v e = do (_, vs, _) <- idR
                   if v `elem` vs
                    then fail "variable is shadowed by a case-alternative constructor argument."
                    else altR (substExprR v e)

-- | (let x = e1 in e2) ==> (e2[e1/x]),
--   x must not be free in e1.
letSubstR :: RewriteH CoreExpr
letSubstR =  prefixFailMsg "Let substition failed: " $
             rewrite $ \ c expr -> case occurAnalyseExpr expr of
                                     Let (NonRec b be) e -> apply (substExprR b be) c e
                                     _ -> fail "expression is not a non-recursive Let."


-- Neil: Commented this out as it's not (currently) used.
--  Perform let-substitution the specified number of times.
-- letSubstNR :: Int -> RewriteH Core
-- letSubstNR 0 = idR
-- letSubstNR n = childR 1 (letSubstNR (n - 1)) >>> promoteExprR letSubstR

-- | This is quite expensive (O(n) for the size of the sub-tree).
safeLetSubstR :: RewriteH CoreExpr
safeLetSubstR =  prefixFailMsg "Safe let-substition failed: " $
                 translate $ \ env expr ->
    let   -- Lit?
          safeBind (Var {})   = True
          safeBind (Lam {})   = True
          safeBind e@(App {}) =
                 case collectArgs e of
                   (Var f,args) -> arityOf env f > length (filter (not . isTyCoArg) args) -- Neil: I've changed this to "not . isTyCoArg" rather than "not . isTypeArg".  This may not be the right thing to do though.
                   (other,args) -> case collectBinders other of
                                     (bds,_) -> length bds > length args
          safeBind _          = False

          safeSubst NoOccInfo = False   -- unknown!
          safeSubst IAmDead   = True    -- DCE
          safeSubst (OneOcc inLam oneBr _) = not inLam && oneBr -- do not inline inside a lambda or if in multiple case branches
          safeSubst _ = False   -- strange case, like a loop breaker
   in case occurAnalyseExpr expr of
      -- By (our) definition, types are a trivial bind
      Let (NonRec b _) _
         | isTyVar b -> apply letSubstR env expr
      Let (NonRec b be) _
         | isId b && (safeBind be || safeSubst (occInfo (idInfo b)))
                     -> apply letSubstR env expr
         | otherwise -> fail "safety critera not met."
      _ -> fail "expression is not a non-recursive Let."

-- | 'safeLetSubstPlusR' tries to inline a stack of bindings, stopping when reaches
-- the end of the stack of lets.
safeLetSubstPlusR :: RewriteH CoreExpr
safeLetSubstPlusR = tryR (letT idR safeLetSubstPlusR Let) >>> safeLetSubstR

------------------------------------------------------------------------

info :: TranslateH Core String
info = translate $ \ c core -> do
         dynFlags <- getDynFlags
         let pa       = "Path: " ++ show (absPath c)
             node     = "Node: " ++ coreNode core
             con      = "Constructor: " ++ coreConstructor core
             bds      = "Bindings in Scope: " ++ show (map unqualifiedVarName $ boundVars c)
             expExtra = case core of
                          ExprCore e -> ["Type or Kind: " ++ showExprTypeOrKind dynFlags e] ++
                                        ["Free Variables: " ++ showVars (coreExprFreeVars e)]
                                           --  ++
                                           -- case e of
                                           --   Var v -> ["Identifier Info: " ++ showIdInfo dynFlags v] -- TODO: what if this is a TyVar?
                                           --   _     -> []
                          _          -> []

         return (intercalate "\n" $ [pa,node,con,bds] ++ expExtra)

showExprTypeOrKind :: DynFlags -> CoreExpr -> String
showExprTypeOrKind dynFlags = showPpr dynFlags . exprTypeOrKind

-- showIdInfo :: DynFlags -> Id -> String
-- showIdInfo dynFlags v = showSDoc dynFlags $ ppIdInfo v $ idInfo v

coreNode :: Core -> String
coreNode (GutsCore _)  = "Module"
coreNode (ProgCore _)  = "Program"
coreNode (BindCore _)  = "Binding Group"
coreNode (DefCore _)   = "Recursive Definition"
coreNode (ExprCore _)  = "Expression"
coreNode (AltCore _)   = "Case Alternative"

coreConstructor :: Core -> String
coreConstructor (GutsCore _)     = "ModGuts"
coreConstructor (ProgCore prog)  = case prog of
                                     ProgNil      -> "ProgNil"
                                     ProgCons _ _ -> "ProgCons"
coreConstructor (BindCore bnd)   = case bnd of
                                     Rec _      -> "Rec"
                                     NonRec _ _ -> "NonRec"
coreConstructor (DefCore _)      = "Def"
coreConstructor (AltCore _)      = "(,,)"
coreConstructor (ExprCore expr)  = case expr of
                                     Var _        -> "Var"
                                     Type _       -> "Type"
                                     Lit _        -> "Lit"
                                     App _ _      -> "App"
                                     Lam _ _      -> "Lam"
                                     Let _ _      -> "Let"
                                     Case _ _ _ _ -> "Case"
                                     Cast _ _     -> "Cast"
                                     Tick _ _     -> "Tick"
                                     Coercion _   -> "Coercion"

------------------------------------------------------------------------

-- | Output a list of all free variables in an expression.
freeIdsQuery :: TranslateH CoreExpr String
freeIdsQuery = do frees <- freeIdsT
                  return $ "Free identifiers are: " ++ showVars frees

-- | Show a human-readable version of a list of 'Var's.
showVars :: [Var] -> String
showVars = show . map var2String

-- | Lifted version of 'coreExprFreeIds'.
freeIdsT :: TranslateH CoreExpr [Id]
freeIdsT = arr coreExprFreeIds

-- | Lifted version of 'coreExprFreeVars'.
freeVarsT :: TranslateH CoreExpr [Var]
freeVarsT = arr coreExprFreeVars

-- | List all free variables (including types) in the expression.
coreExprFreeVars :: CoreExpr -> [Var]
coreExprFreeVars  = uniqSetToList . exprFreeVars

-- | List all free identifiers (value-level free variables) in the expression.
coreExprFreeIds :: CoreExpr -> [Id]
coreExprFreeIds  = uniqSetToList . exprFreeIds

-- | The free variables in a case alternative, which excludes any identifiers bound in the alternative.
altFreeVarsT :: TranslateH CoreAlt [Var]
altFreeVarsT = altT freeVarsT (\ _ vs fvs -> fvs \\ vs)

-- | A variant of 'altFreeVarsT' that returns a function that accepts the case wild-card binder before giving a result.
--   This is so we can use this with congruence combinators, for example:
--
--   caseT id (const altFreeVarsT) $ \ _ wild _ fvs -> [ f wild | f <- fvs ]
altFreeVarsExclWildT :: TranslateH CoreAlt (Id -> [Var])
altFreeVarsExclWildT = altT freeVarsT (\ _ vs fvs wild -> fvs \\ (wild : vs))

------------------------------------------------------------------------

-- | [from GHC documentation] De-shadowing the program is sometimes a useful pre-pass.
-- It can be done simply by running over the bindings with an empty substitution,
-- becuase substitution returns a result that has no-shadowing guaranteed.
--
-- (Actually, within a single /type/ there might still be shadowing, because
-- 'substTy' is a no-op for the empty substitution, but that's probably OK.)
deShadowProgR :: RewriteH CoreProg
deShadowProgR = arr (bindsToProg . deShadowBinds . progToBinds)

------------------------------------------------------------------------
{-
lookupRule :: (Activation -> Bool)	-- When rule is active
	    -> IdUnfoldingFun		-- When Id can be unfolded
            -> InScopeSet
	    -> Id -> [CoreExpr]
	    -> [CoreRule] -> Maybe (CoreRule, CoreExpr)
-}

-- Neil: Commented this out as its not (currently) used.
-- rulesToEnv :: [CoreRule] -> Map.Map String (RewriteH CoreExpr)
-- rulesToEnv rs = Map.fromList
--         [ ( unpackFS (ruleName r), rulesToRewriteH [r] )
--         | r <- rs
--         ]

rulesToRewriteH :: [CoreRule] -> RewriteH CoreExpr
rulesToRewriteH rs = translate $ \ c e -> do
    -- First, we normalize the lhs, so we can match it
    (Var fn,args) <- return $ collectArgs e
    -- Question: does this include Id's, or Var's (which include type names)
    -- Assumption: Var's.
    let in_scope = mkInScopeSet (mkVarEnv [ (v,v) | v <- coreExprFreeVars e ])
        -- The rough_args are just an attempt to try eliminate silly things
        -- that will never match
        _rough_args = map (const Nothing) args   -- rough_args are never used!!! FIX ME!
    -- Finally, we try match the rules
    -- trace (showSDoc (ppr fn GhcPlugins.<+> ppr args $$ ppr rs)) $
#if __GLASGOW_HASKELL__ > 706
    dflags <- getDynFlags
    case lookupRule dflags (const True) (const NoUnfolding) in_scope fn args [r | r <- rs, ru_fn r == idName fn] of
#else
    case lookupRule (const True) (const NoUnfolding) in_scope fn args [r | r <- rs, ru_fn r == idName fn] of
#endif
        Nothing         -> fail "rule not matched"
        Just (r, expr)  -> do
            let e' = mkApps expr (drop (ruleArity r) args)
            ifM (liftM (and . map (inScope c)) $ apply freeVarsT c e')
                (return e')
                (fail $ unlines ["Resulting expression after rule application contains variables that are not in scope."
                                ,"This can probably be solved by running the flatten-module command at the top level."])

-- | Determine whether an identifier is in scope.
inScope :: HermitC -> Id -> Bool
inScope c v = (v `boundIn` c) ||                 -- defined in this module
              case unfoldingInfo (idInfo v) of
                CoreUnfolding {} -> True         -- defined elsewhere
                DFunUnfolding {} -> True
                _                -> False

-- | Lookup a rule and attempt to construct a corresponding rewrite.
rule :: String -> RewriteH CoreExpr
rule r = do
    theRules <- getHermitRules
    case lookup r theRules of
        Nothing -> fail $ "failed to find rule: " ++ show r
        Just rr -> rulesToRewriteH rr

rules :: [String] -> RewriteH CoreExpr
rules = orR . map rule

getHermitRules :: TranslateH a [(String, [CoreRule])]
getHermitRules = contextonlyT $ \ c -> do
    rb     <- liftCoreM getRuleBase
    hscEnv <- liftCoreM getHscEnv
    rb'    <- liftM eps_rule_base $ liftIO $ runIOEnv () $ readMutVar (hsc_EPS hscEnv)
    return [ ( unpackFS (ruleName r), [r] )
           | r <- hermitC_coreRules c ++ concat (nameEnvElts rb) ++ concat (nameEnvElts rb')
           ]

rules_help :: TranslateH Core String
rules_help = do
    rulesEnv <- getHermitRules
    dynFlags <- constT getDynFlags
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
addCoreBindAsRule :: String -> TH.Name -> RewriteH ModGuts
addCoreBindAsRule rule_name nm = contextfreeT $ \ modGuts ->
        case [ (v,e)
             | top_bnds <- mg_binds modGuts
             , (v,e) <- case top_bnds of
                            Rec bnds -> bnds
                            NonRec b e -> [(b,e)]
             ,  nm `cmpTHName2Var` v
             ] of
         [] -> fail $ "cannot find binding " ++ show nm
         [(v,e)] -> return $ modGuts { mg_rules = mg_rules modGuts
                                              ++ [makeRule rule_name v e]
                                     }
         _ -> fail $ "found multiple bindings for " ++ show nm

----------------------------------------------------------------------

-- | Performs dependency anlaysis on an expression.
--   This can be useful to simplify a non-recursive recursive binding group to a non-recursive binding group.
occurAnalyseExpr :: CoreExpr -> CoreExpr
occurAnalyseExpr = OccurAnal.occurAnalyseExpr

-- | Lifted version of 'occurAnalyseExpr'
occurAnalyseExprR :: RewriteH CoreExpr
occurAnalyseExprR = arr occurAnalyseExpr




{- Does not work (no export)
-- Here is a hook into the occur analysis, and a way of looking at the result
occAnalysis ::  CoreExpr -> UsageDetails
occAnalysis = fst . occAnal (initOccEnv all_active_rules)

lookupUsageDetails :: UsageDetails -> Var -> Maybe OccInfo
lookupUsageDetails = lookupVarEnv

-}


exprEqual :: CoreExpr -> CoreExpr -> Bool
exprEqual e1 e2 = eqExpr (mkInScopeSet $ exprsFreeVars [e1, e2]) e1 e2

exprsEqual :: [CoreExpr] -> Bool
exprsEqual = equivalent exprEqual

-- Drew: surely this exists generally somewhere?
-- for instance:
--      equivalent ((==) `on` length) :: [[a]] -> Bool
-- checks if all lists have the same length
equivalent :: (a -> a -> Bool) -> [a] -> Bool
equivalent _  []     = True
equivalent eq (x:xs) = all (eq x) xs

-- The ideas for this function are directly extracted from
-- the GHC function, CoreUtils.eqExprX
bindEqual :: CoreBind -> CoreBind -> Maybe Bool
bindEqual  (Rec ps1) (Rec ps2) = Just $ all2 (eqExprX id_unf env') rs1 rs2
      where
        id_unf _ = noUnfolding      -- Don't expand
        (bs1,rs1) = unzip ps1
        (bs2,rs2) = unzip ps2
        env = mkInScopeSet $ exprsFreeVars (rs1 ++ rs2) -- emptyInScopeSet
        env' = rnBndrs2 (mkRnEnv2 env) bs1 bs2

bindEqual  (NonRec _ e1) (NonRec _ e2) = Just $ exprEqual e1 e2

bindEqual _ _ = Nothing

--------------------------------------------------------

coreEqual :: Core -> Core -> Maybe Bool
coreEqual (ExprCore e1) (ExprCore e2) = Just $ e1 `exprEqual` e2
coreEqual (BindCore b1) (BindCore b2) = b1 `bindEqual` b2
coreEqual (DefCore dc1) (DefCore dc2) = defsToRecBind [dc1] `bindEqual` defsToRecBind [dc2]
coreEqual _             _             = Nothing

compareValues :: TH.Name -> TH.Name -> TranslateH Core ()
compareValues n1 n2 = do
        p1 <- onePathToT (namedBinding n1)
        p2 <- onePathToT (namedBinding n2)
        e1 <- pathT p1 idR
        e2 <- pathT p2 idR
        case e1 `coreEqual` e2 of
          Nothing    -> fail $ show n1 ++ " and " ++ show n2 ++ " are incomparable."
          Just False -> fail $ show n1 ++ " and " ++ show n2 ++ " are not equal."
          Just True  -> return ()

--------------------------------------------------------

-- | Try to figure out the arity of an identifier.
arityOf :: HermitC -> Id -> Int
arityOf env nm =
     case lookupHermitBinding nm env of
        Nothing       -> idArity nm
        Just (DISEMBODIED {}) -> 0
        -- Note: the exprArity will call idArity if
        -- it hits an id; perhaps we should do the counting
        -- The advantage of idArity is it will terminate, though.
        Just (BIND _ _ e)     -> exprArity e
        Just (CASEWILD _ e _) -> exprArity e

-------------------------------------------

-- | Run the Core Lint typechecker.
-- Fails on errors, with error messages.
-- Succeeds returning warnings.
lintModuleT :: TranslateH ModGuts String
lintModuleT = arr (bindsToProg . mg_binds) >>> lintProgramT

lintProgramT :: TranslateH CoreProg String
lintProgramT = do
    bnds <- arr progToBinds
    dflags <- constT getDynFlags
    let (warns, errs) = CoreLint.lintCoreBindings bnds
        dumpSDocs endMsg = Bag.foldBag (\d r -> d ++ ('\n':r)) (showSDoc dflags) endMsg
    if Bag.isEmptyBag errs
        then return $ dumpSDocs "Core Lint Passed" warns
        else observeR (dumpSDocs "" errs) >>> fail "Core Lint Failed"

-- | Note: this can miss several things that a whole-module core lint will find.
-- For instance, running this on the RHS of a binding, the type of the RHS will
-- not be checked against the type of the binding. Running on the whole let expression
-- will catch that however.
lintExprT :: TranslateH CoreExpr String
lintExprT = translate $ \ c e -> do
    dflags <- getDynFlags
    maybe (return "Core Lint Passed") (fail . showSDoc dflags)
                 $ CoreLint.lintUnfolding noSrcLoc (keys $ hermitC_bindings c) e
