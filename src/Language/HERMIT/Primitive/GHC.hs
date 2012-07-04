{-# LANGUAGE ScopedTypeVariables #-}
module Language.HERMIT.Primitive.GHC where

import GhcPlugins hiding (freeVars,empty)
import qualified Language.HERMIT.GHC as GHC
import qualified OccurAnal
import Control.Arrow
import Control.Applicative
import qualified Data.Map as Map

-- import Language.HERMIT.Primitive.Debug
import Language.HERMIT.Primitive.Consider

import Language.HERMIT.Kure
import Language.HERMIT.External
import Language.HERMIT.Context
-- import Language.HERMIT.GHC

import qualified Language.Haskell.TH as TH
-- import Debug.Trace

import Prelude hiding (exp)

------------------------------------------------------------------------

externals :: ModGuts -> [External]
externals modGuts = map (.+ TODO)
         [ external "let-subst" (promoteR letSubstR :: RewriteH Core)
                [ "Let substitution [via GHC]"
                , "let x = E1 in E2 ==> E2[E1/x], fails otherwise"
                , "only matches non-recursive lets" ]                           .+ Deep
         , external "safe-let-subst" (promoteR safeLetSubstR :: RewriteH Core)
                [ "Safe let substitution [via GHC]"
                , "let x = E1 in E2, safe to inline without duplicating work ==> E2[E1/x],"
                , "fails otherwise"
                , "only matches non-recursive lets" ]                           .+ Deep .+ Eval
         , external "safe-let-subst-plus" (promoteR safeLetSubstPlusR :: RewriteH Core)
                [ "Safe let substitution [via GHC]"
                , "let { x = E1, ... } in E2, "
                , "  where safe to inline without duplicating work ==> E2[E1/x,...],"
                , "fails otherwise"
                , "only matches non-recursive lets" ]  .+ Deep .+ Eval
         , external "freevars" (promoteT freeIdsQuery :: TranslateH Core String)
                [ "List the free variables in this expression [via GHC]" ] .+ Query .+ Deep
         , external "deshadow-binds" (promoteR deShadowBindsR :: RewriteH Core)
                [ "Deshadow a program " ] .+ Deep
         , external "apply-rule" (promoteR . rules rulesEnv :: String -> RewriteH Core)
                [ "apply a named GHC rule" ] .+ Shallow
         , external "apply-rule" (rules_help rulesEnv)
                [ "list rules that can be used" ] .+ Query
         , external "compare-values" compareValues
                ["compare's the rhs of two values"] .+ Query .+ Predicate
         ]
  where
          rulesEnv :: Map.Map String (RewriteH CoreExpr)
          rulesEnv = rulesToEnv (mg_rules modGuts ++ other_rules)

          other_rules = [ rule
                        | top_bnds <- mg_binds modGuts
                        , bnd <- case top_bnds of
                                     Rec bnds -> map fst bnds
                                     NonRec b _ -> [b]
                        , rule <- idCoreRules bnd
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

-- output a list of all free variables in the Expr.
freeIdsQuery :: TranslateH CoreExpr String
freeIdsQuery = freeIdsT >>^ (("FreeVars are: " ++) . show . map (showSDoc.ppr))

freeIdsT :: TranslateH CoreExpr [Id]
freeIdsT = arr freeIds

freeVarsT :: TranslateH CoreExpr [Id]
freeVarsT = arr freeVars

-- note: exprFreeVars get *all* free variables, including types
-- note: shadows the freeVars in GHC that operates on the AnnCore.
-- TODO: we should rename this.
freeVars :: CoreExpr -> [Id]
freeVars  = uniqSetToList . exprFreeVars

-- note: exprFreeIds is only value-level free variables
freeIds :: CoreExpr -> [Id]
freeIds  = uniqSetToList . exprFreeIds

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
    let in_scope = mkInScopeSet (mkVarEnv [ (v,v) | v <- freeVars e ])
        -- The rough_args are just an attempt to try eliminate silly things
        -- that will never match
        _rough_args = map (const Nothing) args   -- rough_args are never used!!! FIX ME!
    -- Finally, we try match the rules
    -- trace (showSDoc (ppr fn GhcPlugins.<+> ppr args $$ ppr rs)) $
    case lookupRule (const True) (const NoUnfolding) in_scope fn args rs of
        Nothing         -> fail "rule not matched"
        Just (rule,e')  -> return $ mkApps e' (drop (ruleArity rule) args)

rules :: Map.Map String (RewriteH CoreExpr) -> String -> RewriteH CoreExpr
rules mp r = case Map.lookup r mp of
               Nothing -> fail $ "failed to find rule: " ++ show r
               Just rr -> rr

rules_help :: Map.Map String (RewriteH CoreExpr) -> String
rules_help env = show (Map.keys env)

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
exprEqual (Var v1)       (Var v2)        = Just (v1 == v2)
exprEqual (Lit i1)       (Lit i2)        = Just (i1 == i2)
exprEqual (Type t1)      (Type t2)       = Just (t1 `eqType` t2)
exprEqual (App f1 e1)    (App f2 e2)     = liftA2 (&&) (f1 `exprEqual` f2) (e1 `exprEqual` e2)
exprEqual (Lam _ _)      (Lam _ _)       = Nothing
exprEqual (Case _ _ _ _) (Case _ _ _ _)  = Nothing
exprEqual (Let _ _)      (Let _ _)       = Nothing
exprEqual (Cast _ _)     (Cast _ _)      = Nothing
exprEqual (Tick _ _)     (Tick _ _)      = Nothing
exprEqual (Coercion _)   (Coercion _)    = Nothing
exprEqual _              _               = Just False

coreEqual :: Core -> Core -> Maybe Bool
coreEqual (ExprCore e1) (ExprCore e2) = e1 `exprEqual` e2
coreEqual _             _             = Nothing

-- exprEqual :: CoreExpr -> TranslateH CoreExpr ()
-- exprEqual (Var v1) = do { Var v2 <- idR ; if v1 == v2 then return () else fail "var mismatch" }
-- exprEqual (Lit i1) = do { Lit i2 <- idR ; if i1 == i2 then return () else fail "lit mismatch" }
-- exprEqual (Type t1) = do { Type t2 <- idR ; if t1 `eqType` t2 then return () else fail "type mismatch" }
-- exprEqual (App e1 e2) = appT (exprEqual e1) (exprEqual e2) $ \ () () -> ()
-- exprEqual _        = fail "exprEqual fail"

-- coreEqualT :: Core -> TranslateH Core ()
-- coreEqualT (ModGutsCore  _) = fail "cannot compare ModGuts"
-- coreEqualT (ProgramCore  _) = fail "cannot compare Program"
-- coreEqualT (BindCore  _)    = fail "cannot compare Bind"
-- coreEqualT (DefCore  _)     = fail "cannot compare Def"
-- coreEqualT (ExprCore  e)    = promoteT $ exprEqual e
-- coreEqualT (AltCore  _)     = fail "cannot compare Alt"


-- TODO: make this handle cmp of recusive functions, by using subst.

compareValues :: TH.Name -> TH.Name -> TranslateH Core ()
compareValues n1 n2 = do
        p1 <- rhsOf n1
        p2 <- rhsOf n2
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


