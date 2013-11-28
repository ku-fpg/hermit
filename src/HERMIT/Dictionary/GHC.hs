{-# LANGUAGE CPP, FlexibleContexts #-}
module HERMIT.Dictionary.GHC
       ( -- * GHC-based Transformations
         -- | This module contains transformations that are reflections of GHC functions, or derived from GHC functions.
         externals
         -- ** Substitution
       , substR
       , substCoreAlt
       , substCoreExpr
         -- ** Utilities
 --      , inScope
       , dynFlagsT
       , arityOf
         -- ** Lifted GHC capabilities
         -- A zombie is an identifer that has 'OccInfo' 'IAmDead', but still has occurrences.
       , lintExprT
       , lintModuleT
       , occurAnalyseR
       , occurAnalyseChangedR
       , occurAnalyseExprChangedR
       , occurAnalyseAndDezombifyR
       , dezombifyR
       )
where

import qualified Bag
import qualified CoreLint

import Control.Arrow

import Data.List (mapAccumL)

import HERMIT.Core
import HERMIT.Context
import HERMIT.Kure
import HERMIT.External
import HERMIT.GHC

import HERMIT.Dictionary.Debug hiding (externals)

------------------------------------------------------------------------

-- | Externals that reflect GHC functions, or are derived from GHC functions.
externals :: [External]
externals =
         [ external "deshadow-prog" (promoteProgR deShadowProgR :: RewriteH Core)
                [ "Deshadow a program." ] .+ Deep
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
         ]

------------------------------------------------------------------------

-- | Substitute all occurrences of a variable with an expression, in either a program or an expression.
substR :: MonadCatch m => Var -> CoreExpr -> Rewrite c m Core
substR v e = setFailMsg "Can only perform substitution on expressions, case alternatives or programs." $
             promoteExprR (arr $ substCoreExpr v e) <+ promoteProgR (substTopBindR v e) <+ promoteAltR (arr $ substCoreAlt v e)

-- | Substitute all occurrences of a variable with an expression, in an expression.
substCoreExpr :: Var -> CoreExpr -> (CoreExpr -> CoreExpr)
substCoreExpr v e expr =
    -- The InScopeSet needs to include any free variables appearing in the
    -- expression to be substituted.  Constructing a NonRec Let expression
    -- to pass on to exprFeeVars takes care of this, but ...
    -- TODO Is there a better way to do this ???
    let emptySub = mkEmptySubst (mkInScopeSet (localFreeVarsExpr (Let (NonRec v e) expr)))
     in substExpr (text "substCoreExpr") (extendSubst emptySub v e) expr

-- | Substitute all occurrences of a variable with an expression, in a program.
substTopBindR :: Monad m => Var -> CoreExpr -> Rewrite c m CoreProg
substTopBindR v e =  contextfreeT $ \ p -> do
    -- TODO.  Do we need to initialize the emptySubst with bindFreeVars?
    let emptySub =  emptySubst -- mkEmptySubst (mkInScopeSet (exprFreeVars exp))
    return $ bindsToProg $ snd (mapAccumL substBind (extendSubst emptySub v e) (progToBinds p))

-- | Substitute all occurrences of a variable with an expression, in a case alternative.
substCoreAlt :: Var -> CoreExpr -> CoreAlt -> CoreAlt
substCoreAlt v e alt = let (con, vs, rhs) = alt
                           inS            = (flip delVarSet v . unionVarSet (localFreeVarsExpr e) . localFreeVarsAlt) alt
                           subst          = extendSubst (mkEmptySubst (mkInScopeSet inS)) v e
                           (subst', vs')  = substBndrs subst vs
                        in (con, vs', substExpr (text "alt-rhs") subst' rhs)

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
