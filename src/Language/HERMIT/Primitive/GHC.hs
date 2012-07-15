{-# LANGUAGE ScopedTypeVariables, TypeFamilies, FlexibleContexts, TupleSections #-}
module Language.HERMIT.Primitive.GHC where

import GhcPlugins hiding (empty)
import qualified Language.HERMIT.GHC as GHC
import qualified OccurAnal
import Control.Arrow
import Control.Monad
import qualified Data.Map as Map

-- import Language.HERMIT.Primitive.Debug
import Language.HERMIT.Primitive.Navigation

import Language.HERMIT.CoreExtra
import Language.HERMIT.Kure
import Language.HERMIT.Monad
import Language.HERMIT.External
import Language.HERMIT.Context
-- import Language.HERMIT.GHC

import qualified Language.Haskell.TH as TH
-- import Debug.Trace

import Prelude hiding (exp)

------------------------------------------------------------------------

externals :: [External]
externals =
         [ external "let-subst" (promoteExprR letSubstR :: RewriteH Core)
                [ "Let substitution [via GHC]"
                , "let x = E1 in E2 ==> E2[E1/x], fails otherwise"
                , "only matches non-recursive lets" ]                           .+ Deep
         , external "safe-let-subst" (promoteExprR safeLetSubstR :: RewriteH Core)
                [ "Safe let substitution [via GHC]"
                , "let x = E1 in E2, safe to inline without duplicating work ==> E2[E1/x],"
                , "fails otherwise"
                , "only matches non-recursive lets" ]                           .+ Deep .+ Eval .+ Bash
         , external "safe-let-subst-plus" (promoteExprR safeLetSubstPlusR :: RewriteH Core)
                [ "Safe let substitution [via GHC]"
                , "let { x = E1, ... } in E2, "
                , "  where safe to inline without duplicating work ==> E2[E1/x,...],"
                , "fails otherwise"
                , "only matches non-recursive lets" ]  .+ Deep .+ Eval
         , external "free-ids" (promoteExprT freeIdsQuery :: TranslateH Core String)
                [ "List the free identifiers in this expression [via GHC]" ] .+ Query .+ Deep
         , external "deshadow-binds" (promoteProgramR deShadowBindsR :: RewriteH Core)
                [ "Deshadow a program " ] .+ Deep
         , external "apply-rule" (promoteExprR . rules :: String -> RewriteH Core)
                [ "apply a named GHC rule" ] .+ Shallow
         , external "apply-rule" (rules_help :: TranslateH Core String)
                [ "list rules that can be used" ] .+ Query
         , external "compare-values" compareValues
                ["compare's the rhs of two values"] .+ Query .+ Predicate
         , external "add-rule" (\ rule_name id_name -> promoteModGutsR (addCoreBindAsRule rule_name id_name))
                ["add-rule \"rule-name\" <id> -- adds a new rule that freezes the right hand side of the <id>"]
                                        .+ Introduce
         , external "cast-elim" (promoteExprR castElimination)
                ["cast-elim removes casts"]
                                        .+ Shallow .+ TODO
         ]

------------------------------------------------------------------------

letSubstR :: RewriteH CoreExpr
letSubstR = contextfreeT $ \ exp -> case exp of
      Let (NonRec b be) e
         | isId b    -> let emptySub = mkEmptySubst (mkInScopeSet (exprFreeVars exp))
                            sub      = extendSubst emptySub b be
                         in return $ substExpr (text "letSubstR") sub e
      Let (NonRec b (Type bty)) e
         | isTyVar b -> let emptySub = mkEmptySubst (mkInScopeSet (exprFreeVars exp))
                            sub      = extendTvSubst emptySub b bty
                         in return $ substExpr (text "letSubstR") sub e
      _ -> fail "LetSubst failed. Expr is not a (non-recursive) Let."

-- This is quite expensive (O(n) for the size of the sub-tree)
safeLetSubstR :: RewriteH CoreExpr
safeLetSubstR = translate $ \ env exp ->
    let   -- Lit?
          safeBind (Var {})   = True
          safeBind (Lam {})   = True
          safeBind e@(App {}) =
                 case collectArgs e of
                   (Var f,args) -> arityOf env f > length (filter (not . isTypeArg) args)
                   (other,args) -> case collectBinders other of
                                     (bds,_) -> length bds > length args
          safeBind _          = False

          safeSubst NoOccInfo = False   -- unknown!
          safeSubst IAmDead   = True    -- DCE
          safeSubst (OneOcc inLam oneBr _)
                              | inLam == True || oneBr == False = False   -- do not inline inside a lambda
                                                                          -- or if in multiple case branches
                              | otherwise = True
          safeSubst _ = False   -- strange case, like a loop breaker
   in case occurAnalyseExpr exp of
      Let (NonRec b (Type bty)) e
         | isTyVar b -> let emptySub = mkEmptySubst (mkInScopeSet (exprFreeVars exp))
                            sub      = extendTvSubst emptySub b bty
                         in return $ substExpr (text "letSubstR") sub e
      Let (NonRec b be) e
         | isId b && (safeBind be || safeSubst (occInfo (idInfo b)))
                     -> let emptySub = mkEmptySubst (mkInScopeSet (exprFreeVars exp))
                            sub      = extendSubst emptySub b be
                         in return $ substExpr (text "letSubstR") sub e
         | otherwise -> fail "safeLetSubstR failed (safety critera not met)"
      -- By (our) definition, types are a trivial bind
      _ -> fail "LetSubst failed. Expr is not a (non-recursive) Let."

-- | 'safeLetSubstPlusR' tries to inline a stack of bindings, stopping when reaches
-- the end of the stack of lets.
safeLetSubstPlusR :: RewriteH CoreExpr
safeLetSubstPlusR = tryR (letT idR safeLetSubstPlusR Let) >>> safeLetSubstR


------------------------------------------------------------------------

-- | Output a list of all free variables in an expression.
freeIdsQuery :: TranslateH CoreExpr String
freeIdsQuery = freeIdsT >>^ (("Free identifiers are: " ++) . showVars)

-- | Show a human-readable version of a list of 'Var's.
showVar :: Var -> String
showVar = show . showSDoc . ppr

-- | Show a human-readable version of a 'Var'.
showVars :: [Var] -> String
showVars = show . map (showSDoc . ppr)

-- Doesn't work, because it doesn't account for any bindings we add as we navigate down.
-- freeIdsQuery :: TranslateH Core String
-- freeIdsQuery = prunetdT (promoteExprT freeIdsT)
--                >>^ (("Free identifiers are: " ++) . show . map (showSDoc.ppr) . nub)

freeIdsT :: TranslateH CoreExpr [Id]
freeIdsT = arr coreExprFreeIds

freeVarsT :: TranslateH CoreExpr [Var]
freeVarsT = arr coreExprFreeVars

-- note: exprFreeVars get *all* free variables, including types
coreExprFreeVars :: CoreExpr -> [Var]
coreExprFreeVars  = uniqSetToList . exprFreeVars

-- note: exprFreeIds is only value-level free variables
coreExprFreeIds :: CoreExpr -> [Id]
coreExprFreeIds  = uniqSetToList . exprFreeIds

------------------------------------------------------------------------

-- | [from GHC documentation] De-shadowing the program is sometimes a useful pre-pass.
-- It can be done simply by running over the bindings with an empty substitution,
-- becuase substitution returns a result that has no-shadowing guaranteed.
--
-- (Actually, within a single /type/ there might still be shadowing, because
-- 'substTy' is a no-op for the empty substitution, but that's probably OK.)
deShadowBindsR :: RewriteH CoreProgram
deShadowBindsR = arr deShadowBinds

------------------------------------------------------------------------
{-
lookupRule :: (Activation -> Bool)	-- When rule is active
	    -> IdUnfoldingFun		-- When Id can be unfolded
            -> InScopeSet
	    -> Id -> [CoreExpr]
	    -> [CoreRule] -> Maybe (CoreRule, CoreExpr)
-}

rulesToEnv :: [CoreRule] -> Map.Map String (RewriteH CoreExpr)
rulesToEnv rs = Map.fromList
        [ ( unpackFS (ruleName r), rulesToRewriteH [r] )
        | r <- rs
        ]

rulesToRewriteH :: [CoreRule] -> RewriteH CoreExpr
rulesToRewriteH rs = contextfreeT $ \ e -> do
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
    case lookupRule (const True) (const NoUnfolding) in_scope fn args rs of
        Nothing         -> fail "rule not matched"
        Just (rule,e')  -> return $ mkApps e' (drop (ruleArity rule) args)

rules ::  String -> RewriteH CoreExpr
rules r = do
        theRules <- getHermitRules
        case lookup r theRules of
               Nothing -> fail $ "failed to find rule: " ++ show r
               Just rr -> rulesToRewriteH rr

getHermitRules :: (Generic a ~ Core) => TranslateH a [(String, [CoreRule])]
getHermitRules = translate $ \ env _e -> do
    rb <- liftCoreM $ getRuleBase
    let other_rules = [ rule
                        | top_bnds <- mg_binds (hermitModGuts env)
                        , bnd <- case top_bnds of
                                     Rec bnds -> map fst bnds
                                     NonRec b _ -> [b]
                        , rule <- idCoreRules bnd
                        ]
    return [ ( unpackFS (ruleName r), [r] )
           | r <- mg_rules (hermitModGuts env) ++ other_rules ++ concat (nameEnvElts rb)
           ]

rules_help :: TranslateH Core String
rules_help = do
    rulesEnv <- getHermitRules
    return  $ (show (map fst rulesEnv) ++ "\n") ++
              (showSDoc $ pprRulesForUser $ concatMap snd rulesEnv)

makeRule :: String -> Id -> CoreExpr -> CoreRule
makeRule rule_name nm expr =
                          mkRule True   -- auto-generated
                                 False  -- local
                                 (mkFastString rule_name)
                                 NeverActive    -- because we need to call for these
                                 (varName nm)
                                 []
                                 []
                                 expr

-- TODO: check if a top-level binding
addCoreBindAsRule :: String -> TH.Name -> RewriteH ModGuts
addCoreBindAsRule rule_name nm = contextfreeT $ \ modGuts ->
        case [ (v,e)
             | top_bnds <- mg_binds modGuts
             , (v,e) <- case top_bnds of
                            Rec bnds -> bnds
                            NonRec b e -> [(b,e)]
             ,  nm `cmpName` idName v
             ] of
         [] -> fail $ "can not find binding " ++ show nm
         [(v,e)] -> return $ modGuts { mg_rules = mg_rules modGuts
                                              ++ [makeRule rule_name v e]
                                     }
         _ -> fail $ "found multiple bindings for " ++ show nm

  where

----------------------------------------------------------------------

occurAnalyseExpr :: CoreExpr -> CoreExpr
occurAnalyseExpr = OccurAnal.occurAnalyseExpr

{- Does not work (no export)
-- Here is a hook into the occur analysis, and a way of looking at the result
occAnalysis ::  CoreExpr -> UsageDetails
occAnalysis = fst . occAnal (initOccEnv all_active_rules)

lookupUsageDetails :: UsageDetails -> Var -> Maybe OccInfo
lookupUsageDetails = lookupVarEnv

-}

{-
joinT :: TranslateH a (TranslateH b c) -> (a -> TranslateH b c)
joinT f e0 = translate $ \ c e1 -> do
                t <- apply f c e0
                apply t c e1
-}

exprEqual :: CoreExpr -> CoreExpr -> Maybe Bool
exprEqual e1 e2 = Just $ eqExpr (mkInScopeSet $ exprsFreeVars [e1, e2]) e1 e2


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

bindEqual  (NonRec _ e1) (NonRec _ e2) = exprEqual e1 e2

bindEqual _ _ = Nothing

--------------------------------------------------------

coreEqual :: Core -> Core -> Maybe Bool
coreEqual (ExprCore e1) (ExprCore e2) = e1 `exprEqual` e2
coreEqual (BindCore b1) (BindCore b2) = b1 `bindEqual` b2
coreEqual (DefCore dc1) (DefCore dc2) = (defToRecBind [dc1]) `bindEqual` (defToRecBind [dc2])
coreEqual _             _             = Nothing

compareValues :: TH.Name -> TH.Name -> TranslateH Core ()
compareValues n1 n2 = do
        p1 <- onePathToT (namedBinding n1)
        p2 <- onePathToT (namedBinding n2)
        e1 :: Core <- pathT p1 idR
        e2 :: Core <- pathT p2 idR
        case e1 `coreEqual` e2 of
          Nothing    -> fail $ show n1 ++ " and " ++ show n2 ++ " are incomparable"
          Just False -> fail $ show n1 ++ " and " ++ show n2 ++ " are not equal"
          Just True  -> return ()

--------------------------------------------------------


-- try figure out the arity of an Id
arityOf:: Context -> Id -> Int
arityOf env nm =
     case lookupHermitBinding nm env of
        Nothing       -> idArity nm
        Just (LAM {}) -> 0
        -- Note: the exprArity will call idArity if
        -- it hits an id; perhaps we should do the counting
        -- The advantage of idArity is it will terminate, though.
        Just (BIND _ _ e) -> GHC.exprArity e
        Just (CASE _ e _) -> GHC.exprArity e

---------------------------------------------------------


-- TODO: cloneIdH should use this
cloneId :: (String -> String) -> Id -> HermitM Id
cloneId nameMod b = do
        uq <- getUniqueM
        let name = mkSystemVarName uq $ mkFastString $ nameMod $ getOccString b
            ty   = idType b
        return $ mkLocalId name ty

-------------------------------------------

-- remove a cast;
-- TODO: check for validity of removing this cast
castElimination :: RewriteH CoreExpr
castElimination = do
        Cast e _ <- idR
        return $ e

{-
    go (Cast e co)      | isReflCo co' = go e
       	                | otherwise    = Cast (go e) co'
                        where
                          co' = optCoercion (getCvSubst subst) co
-}

