{-# LANGUAGE CPP, FlexibleContexts, ScopedTypeVariables, LambdaCase #-}
module HERMIT.Primitive.GHC
       ( -- * GHC-based Transformations
         -- | This module contains transformations that are reflections of GHC functions, or derived from GHC functions.
         externals
       , anyCallR
         -- ** Free Variables
       , tyVarsOfTypeT
       , exprFreeIdsT
       , exprFreeVarsT
       , bindFreeVarsT
       , altFreeVarsT
       , altFreeVarsExclWildT
         -- ** Substitution
       , substR
       , substExprR
         -- ** Equality
       , coreEqual
       , progEqual
       , bindEqual
       , defEqual
       , exprEqual
       , altEqual
         -- ** Utilities
       , inScope
       , showVarSet
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
       , occurAnalyseAndDezombifyR
       , dezombifyR
       )
where

import GhcPlugins
import qualified Bag
import qualified CoreLint
import IOEnv
import qualified SpecConstr

import Control.Arrow
import Control.Monad

import Data.Function (on)
import Data.List (intercalate,mapAccumL,deleteFirstsBy)
import Data.Monoid (mempty)

import HERMIT.Core
import HERMIT.Context
import HERMIT.Monad
import HERMIT.Kure
import HERMIT.External
import HERMIT.GHC

import HERMIT.Primitive.Debug hiding (externals)
import HERMIT.Primitive.Navigation hiding (externals)

import qualified Language.Haskell.TH as TH

------------------------------------------------------------------------

-- | Externals that reflect GHC functions, or are derived from GHC functions.
externals :: [External]
externals =
         [ external "info" (info :: TranslateH CoreTC String)
                [ "Display information about the current node." ]
         , external "free-ids" (promoteExprT freeIdsQuery :: TranslateH Core String)
                [ "List the free identifiers in this expression." ] .+ Query .+ Deep
         , external "deshadow-prog" (promoteProgR deShadowProgR :: RewriteH Core)
                [ "Deshadow a program." ] .+ Deep
         , external "apply-rule" (promoteExprR . rule :: String -> RewriteH Core)
                [ "Apply a named GHC rule" ] .+ Shallow
         , external "apply-rule" (rules_help :: TranslateH Core String)
                [ "List rules that can be used" ] .+ Query
         , external "apply-rules" (promoteExprR . rules :: [String] -> RewriteH Core)
                [ "Apply named GHC rules, succeed if any of the rules succeed" ] .+ Shallow
         , external "compare-values" (compareValues ::  TH.Name -> TH.Name -> TranslateH Core ())
                [ "Compare the rhs of two values."] .+ Query .+ Predicate
         , external "add-rule" ((\ rule_name id_name -> promoteModGutsR (addCoreBindAsRule rule_name id_name)) :: String -> TH.Name -> RewriteH Core)
                [ "add-rule \"rule-name\" <id> -- adds a new rule that freezes the right hand side of the <id>"]  .+ Introduce
         , external "dezombify" (promoteExprR dezombifyR :: RewriteH Core)
                [ "Zap the occurrence information in the current identifer if it is a zombie."] .+ Shallow .+ Bash
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
         , external "any-call" (anyCallR :: RewriteH Core -> RewriteH Core)
                [ "any-call (.. unfold command ..) applies an unfold command to all applications."
                , "Preference is given to applications with more arguments." ] .+ Deep
         ]

------------------------------------------------------------------------

-- | Substitute all occurrences of a variable with an expression, in either a program or an expression.
substR :: (ExtendPath c Crumb, AddBindings c, MonadCatch m) => Var -> CoreExpr -> Rewrite c m Core
substR v e = setFailMsg "Can only perform substitution on expressions or programs." $
             promoteExprR (substExprR v e) <+ promoteProgR (substTopBindR v e) <+ promoteAltR (substAltR v e)

-- | Substitute all occurrences of a variable with an expression, in an expression.
substExprR :: Monad m => Var -> CoreExpr -> Rewrite c m CoreExpr
substExprR v e =  contextfreeT $ \ expr -> do
    -- The InScopeSet needs to include any free variables appearing in the
    -- expression to be substituted.  Constructing a NonRec Let expression
    -- to pass on to exprFeeVars takes care of this, but ...
    -- TODO Is there a better way to do this ???
    let emptySub = mkEmptySubst (mkInScopeSet (exprFreeVars (Let (NonRec v e) expr)))
    return $ substExpr (text "substR") (extendSubst emptySub v e) expr

-- | Substitute all occurrences of a variable with an expression, in a program.
substTopBindR :: Monad m => Var -> CoreExpr -> Rewrite c m CoreProg
substTopBindR v e =  contextfreeT $ \ p -> do
    -- TODO.  Do we need to initialize the emptySubst with bindFreeVars?
    let emptySub =  emptySubst -- mkEmptySubst (mkInScopeSet (exprFreeVars exp))
    return $ bindsToProg $ snd (mapAccumL substBind (extendSubst emptySub v e) (progToBinds p))

-- | Substitute all occurrences of a variable with an expression, in a case alternative.
substAltR :: (ExtendPath c Crumb, AddBindings c, Monad m) => Var -> CoreExpr -> Rewrite c m CoreAlt
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

info :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, ReadBindings c, BoundVars c, HasDynFlags m, MonadCatch m) => Translate c m CoreTC String
info = do crumbs <- childrenT
          translate $ \ c coreTC -> do
            dynFlags <- getDynFlags
            let pa       = "Path: " ++ showCrumbs (snocPathToPath $ absPath c)
                node     = "Node: " ++ coreTCNode coreTC
                con      = "Constructor: " ++ coreTCConstructor coreTC
                children = "Children: " ++ showCrumbs crumbs
                bds      = "Bindings in Scope: " ++ showVarSet (boundVars c)
                extra    = case coreTC of
                             Core (ExprCore e)      -> let tyK = exprKindOrType e
                                                        in [(if isKind tyK then "Kind: " else "Type: ") ++ showPpr dynFlags tyK] ++
                                                           ["Free Variables: " ++ showVarSet (exprFreeVars e)] ++
                                                           case e of
                                                             Var i -> ["Identifier Arity: " ++ show (arityOf c i)]
                                                             _     -> []
                             TyCo (TypeCore ty)     -> ["Kind: " ++ showPpr dynFlags (typeKind ty)]
                             TyCo (CoercionCore co) -> ["Kind: " ++ showPpr dynFlags (coercionKind co) ]
                             _                      -> []

            return (intercalate "\n" $ [pa,node,con,children,bds] ++ extra)

-- showIdInfo :: DynFlags -> Id -> String
-- showIdInfo dynFlags v = showSDoc dynFlags $ ppIdInfo v $ idInfo v

coreTCNode :: CoreTC -> String
coreTCNode (Core core)           = coreNode core
coreTCNode (TyCo TypeCore{})     = "Type"
coreTCNode (TyCo CoercionCore{}) = "Coercion"

coreNode :: Core -> String
coreNode (GutsCore _)  = "Module"
coreNode (ProgCore _)  = "Program"
coreNode (BindCore _)  = "Binding Group"
coreNode (DefCore _)   = "Recursive Definition"
coreNode (ExprCore _)  = "Expression"
coreNode (AltCore _)   = "Case Alternative"

coreTCConstructor :: CoreTC -> String
coreTCConstructor = \case
                       Core core              -> coreConstructor core
                       TyCo (TypeCore ty)     -> typeConstructor ty
                       TyCo (CoercionCore co) -> coercionConstructor co

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

typeConstructor :: Type -> String
typeConstructor = \case
                     TyVarTy{}    -> "TyVarTy"
                     AppTy{}      -> "AppTy"
                     TyConApp{}   -> "TyConApp"
                     FunTy{}      -> "FunTy"
                     ForAllTy{}   -> "ForAllTy"
                     LitTy{}      -> "LitTy"

coercionConstructor :: Coercion -> String
coercionConstructor = \case
                         Refl{}        -> "Refl"
                         TyConAppCo{}  -> "TyConAppCo"
                         AppCo{}       -> "AppCo"
                         ForAllCo{}    -> "ForAllCo"
                         CoVarCo{}     -> "CoVarCo"
                         AxiomInstCo{} -> "AxiomInstCo"
                         UnsafeCo{}    -> "UnsafeCo"
                         SymCo{}       -> "SymCo"
                         TransCo{}     -> "TransCo"
                         NthCo{}       -> "NthCo"
                         InstCo{}      -> "InstCo"
#if __GLASGOW_HASKELL__ > 706
                         LRCo{}        -> "LRCo"
#endif

------------------------------------------------------------------------

-- | Output a list of all free variables in an expression.
freeIdsQuery :: Monad m => Translate c m CoreExpr String
freeIdsQuery = do frees <- exprFreeIdsT
                  return $ "Free identifiers are: " ++ showVarSet frees

-- | Show a human-readable version of a list of 'Var's.
showVars :: [Var] -> String
showVars = show . map var2String

-- | Show a human-readable version of a 'VarSet'.
showVarSet :: VarSet -> String
showVarSet = showVars . varSetElems

-- | Lifted version of 'exprFreeIds'.
exprFreeIdsT :: Monad m => Translate c m CoreExpr IdSet
exprFreeIdsT = arr exprFreeIds

-- | Lifted version of 'exprFreeVars'.
exprFreeVarsT :: Monad m => Translate c m CoreExpr VarSet
exprFreeVarsT = arr exprFreeVars

-- | Lifted version of 'tyVarsOfType'.
tyVarsOfTypeT :: Monad m => Translate c m Type TyVarSet
tyVarsOfTypeT = arr tyVarsOfType

-- | The free variables in a case alternative, which excludes any variables bound in the alternative.
altFreeVarsT :: (ExtendPath c Crumb, AddBindings c, Monad m) => Translate c m CoreAlt VarSet
altFreeVarsT = altT mempty (\ _ -> idR) exprFreeVarsT (\ () vs fvs -> delVarSetList fvs vs)

-- | The free variables in a binding group, which excludes any variables bound in the group.
bindFreeVarsT :: (ExtendPath c Crumb, AddBindings c, MonadCatch m) => Translate c m CoreBind VarSet
bindFreeVarsT = nonRecT idR exprFreeVarsT (\ v fvs -> delVarSet fvs v)
                <+ recDefT (\ _ -> (idR, exprFreeVarsT)) (uncurry (flip delVarSetList) . second unionVarSets . unzip)

-- | A variant of 'altFreeVarsT' that returns a function that accepts the case wild-card binder before giving a result.
--   This is so we can use this with congruence combinators, for example:
--
--   caseT id (const altFreeVarsT) $ \ _ wild _ fvs -> [ f wild | f <- fvs ]
altFreeVarsExclWildT :: (ExtendPath c Crumb, AddBindings c, Monad m) => Translate c m CoreAlt (Id -> VarSet)
altFreeVarsExclWildT = altT mempty (\ _ -> idR) exprFreeVarsT (\ () vs fvs wild -> delVarSetList fvs (wild : vs))

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
rulesToRewriteH :: (ReadBindings c, HasDynFlags m, Monad m) => [CoreRule] -> Rewrite c m CoreExpr
#else
rulesToRewriteH :: (ReadBindings c, Monad m) => [CoreRule] -> Rewrite c m CoreExpr
#endif
rulesToRewriteH rs = translate $ \ c e -> do
    -- First, we normalize the lhs, so we can match it
    (Var fn,args) <- return $ collectArgs e
    -- Question: does this include Id's, or Var's (which include type names)
    -- Assumption: Var's.
    let in_scope = mkInScopeSet (mkVarEnv [ (v,v) | v <- varSetElems (exprFreeVars e) ])
        -- The rough_args are just an attempt to try eliminate silly things
        -- that will never match
        _rough_args = map (const Nothing) args   -- rough_args are never used!!! FIX ME!
    -- Finally, we try match the rules
    -- trace (showSDoc (ppr fn GhcPlugins.<+> ppr args $$ ppr rs)) $
#if __GLASGOW_HASKELL__ > 706
    dflags <- getDynFlags
    case lookupRule dflags (in_scope, const NoUnfolding) (const True) fn args [r | r <- rs, ru_fn r == idName fn] of
#else
    case lookupRule (const True) (const NoUnfolding) in_scope fn args [r | r <- rs, ru_fn r == idName fn] of
#endif
        Nothing         -> fail "rule not matched"
        Just (r, expr)  -> do
            let e' = mkApps expr (drop (ruleArity r) args)
            ifM (liftM (and . map (inScope c) . varSetElems) $ apply exprFreeVarsT c e')
                (return e')
                (fail $ unlines ["Resulting expression after rule application contains variables that are not in scope."
                                ,"This can probably be solved by running the flatten-module command at the top level."])

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

---------------------------------------------------------------

-- | Alpha equality of programs.
progEqual :: CoreProg -> CoreProg -> Bool
progEqual ProgNil ProgNil                       = True
progEqual (ProgCons bnd1 p1) (ProgCons bnd2 p2) = bindEqual bnd1 bnd2 && progEqual p1 p2
progEqual _ _                                   = False

-- The ideas for this function are directly extracted from
-- the GHC function, CoreUtils.eqExprX
-- | Alpha equality of binding groups.
bindEqual :: CoreBind -> CoreBind -> Bool
bindEqual (NonRec _ e1) (NonRec _ e2) = exprEqual e1 e2
bindEqual (Rec ps1)     (Rec ps2)     = all2 (eqExprX id_unf env) rs1 rs2
  where
    id_unf _   = noUnfolding      -- Don't expand
    (bs1,rs1)  = unzip ps1
    (bs2,rs2)  = unzip ps2
    inScopeSet = mkInScopeSet $ exprsFreeVars (rs1 ++ rs2)
    env        = rnBndrs2 (mkRnEnv2 inScopeSet) bs1 bs2
bindEqual _ _ = False

-- | Alpha equality of recursive definitions.
defEqual :: CoreDef -> CoreDef -> Bool
defEqual d1 d2 = defsToRecBind [d1] `bindEqual` defsToRecBind [d2]

-- | Alpha equality of expressions.
exprEqual :: CoreExpr -> CoreExpr -> Bool
exprEqual e1 e2 = eqExpr (mkInScopeSet $ exprsFreeVars [e1, e2]) e1 e2

-- The ideas for this function are directly extracted from
-- the GHC function, CoreUtils.eqExprX
-- | Alpha equality of case alternatives.
altEqual :: CoreAlt -> CoreAlt -> Bool
altEqual (c1,vs1,e1) (c2,vs2,e2) = c1 == c2 && eqExprX id_unf env e1 e2
  where
    id_unf _    = noUnfolding      -- Don't expand
    inScopeSet  = mkInScopeSet $ exprsFreeVars [e1,e2]
    env         = rnBndrs2 (mkRnEnv2 inScopeSet) vs1 vs2

-- | Alpha equality of 'Core' fragments.
coreEqual :: Core -> Core -> Bool
coreEqual (GutsCore g1) (GutsCore g2) = bindsToProg (mg_binds g1) `progEqual` bindsToProg (mg_binds g2)
coreEqual (ProgCore p1) (ProgCore p2) = progEqual p1 p2
coreEqual (BindCore b1) (BindCore b2) = bindEqual b1 b2
coreEqual (DefCore d1)  (DefCore d2)  = defEqual d1 d2
coreEqual (ExprCore e1) (ExprCore e2) = exprEqual e1 e2
coreEqual (AltCore a1) (AltCore a2)   = altEqual a1 a2
coreEqual _             _             = False

--------------------------------------------------------

compareValues :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, MonadCatch m) => TH.Name -> TH.Name -> Translate c m Core ()
compareValues n1 n2 = do -- TODO: this can be made more efficient by performing a single traversal.  But I'm not sure of the intent.  What should happen if two things match a name?
        p1 <- onePathToT (arr $ namedBinding n1)
        p2 <- onePathToT (arr $ namedBinding n2)
        e1 <- localPathT p1 idR
        e2 <- localPathT p2 idR
        guardMsg (e1 `coreEqual` e2) (show n1 ++ " and " ++ show n2 ++ " are not equal.")

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
     let (warns, errs)    = CoreLint.lintCoreBindings bnds
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
                 $ CoreLint.lintUnfolding noSrcLoc (varSetElems $ boundVars c) e

specConstrR :: RewriteH ModGuts
specConstrR = do
    rs  <- extractT specRules
    e'  <- contextfreeT $ liftCoreM . SpecConstr.specConstrProgram
    rs' <- return e' >>> extractT specRules
    let specRs = deleteFirstsBy ((==) `on` ru_name) rs' rs
    return e' >>> extractR (repeatR (anyCallR (promoteExprR $ rulesToRewriteH specRs)))

-- | Get all the specialization rules on a binding.
--   These are created by SpecConstr and other GHC passes.
idSpecRules :: TranslateH Id [CoreRule]
idSpecRules = contextfreeT $ \ i -> let SpecInfo rs _ = specInfo (idInfo i) in return rs

-- | Promote 'idSpecRules' to CoreBind.
bindSpecRules :: TranslateH CoreBind [CoreRule]
bindSpecRules =    recT (\_ -> defT idSpecRules (return ()) const) concat
                <+ nonRecT idSpecRules (return ()) const

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
occurAnalyseR :: (AddBindings c, ExtendPath c Crumb, MonadCatch m) => Rewrite c m Core
occurAnalyseR = let r  = promoteExprR (arr occurAnalyseExpr)
                    go = r <+ anyR go
                 in tryR go -- always succeed

-- | Apply 'occurAnalyseExprR' to all sub-expressions, failing if the result is alpha-equivalent to the original.
occurAnalyseChangedR :: (AddBindings c, ExtendPath c Crumb, MonadCatch m) => Rewrite c m Core
occurAnalyseChangedR = changedByR coreEqual occurAnalyseR

-- | Run GHC's occurrence analyser, and also eliminate any zombies.
occurAnalyseAndDezombifyR :: (AddBindings c, ExtendPath c Crumb, MonadCatch m) => Rewrite c m Core
occurAnalyseAndDezombifyR = allbuR (tryR $ promoteExprR dezombifyR) >>> occurAnalyseR

occurrenceAnalysisR :: (AddBindings c, ExtendPath c Crumb, MonadCatch m) => Rewrite c m Core
occurrenceAnalysisR = occurAnalyseAndDezombifyR

{- Does not work (no export)
-- Here is a hook into the occur analysis, and a way of looking at the result
occAnalysis ::  CoreExpr -> UsageDetails
occAnalysis = fst . occAnal (initOccEnv all_active_rules)

lookupUsageDetails :: UsageDetails -> Var -> Maybe OccInfo
lookupUsageDetails = lookupVarEnv

-}

----------------------------------------------------------------------
