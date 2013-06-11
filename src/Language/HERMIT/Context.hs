{-# LANGUAGE InstanceSigs, ConstraintKinds, MultiParamTypeClasses #-}

module Language.HERMIT.Context
       ( -- * HERMIT Contexts
         -- ** The Standard Context
         HermitC
       , initHermitC
         -- ** Bindings
       , HermitBindingSite(..)
       , BindingDepth
       , HermitBinding
       , hermitBindingSiteExpr
       , hermitBindingExpr
         -- ** Adding bindings to contexts
       , AddBindings(..)
       , addBindingGroup
       , addLambdaBinding
       , addAltBindings
       , addCaseWildBinding
       , addForallBinding
         -- ** Reading bindings from the context
       , ReadBindings(..)
       , lookupHermitBinding
       , boundVars
       , boundIn
       , findBoundVars
         -- ** Accessing the Global Reader Environment from the context
       , HasGlobalRdrEnv(..)
         -- ** Accessing GHC rewrite rules from the context
       , HasCoreRules(..)
) where

import Prelude hiding (lookup)
import GhcPlugins hiding (empty)
import Data.Monoid (mempty)
import Data.Map hiding (map, foldr, filter)
import qualified Language.Haskell.TH as TH

import Language.KURE

import Language.HERMIT.Core
import Language.HERMIT.GHC

------------------------------------------------------------------------

-- | The depth of a binding.  Used, for example, to detect shadowing when inlining.
type BindingDepth = Int


-- | HERMIT\'s representation of variable bindings.
--   Bound expressions cannot be inlined without checking for shadowing issues (using the depth information).
data HermitBindingSite
        = REC CoreExpr
        | NONREC CoreExpr
        | LAM
        | CASEALT
        | FORALL
        | CASEWILD CoreExpr (AltCon,[Var])  -- ^ We store both the scrutinised expression, and the case alternative 'AltCon' (which can be converted to Constructor or Literal) and variables.

type HermitBinding = (BindingDepth, HermitBindingSite)

-- | Retrieve the expression in a 'HermitBindingSite', if there is one.
hermitBindingSiteExpr :: HermitBindingSite -> Maybe CoreExpr
hermitBindingSiteExpr b = case b of
                            REC e        -> Just e
                            NONREC e     -> Just e
                            CASEWILD e _ -> Just e
                            _            -> Nothing
{-# INLINE hermitBindingSiteExpr #-}

-- | Retrieve the expression in a 'HermitBinding', if there is one.
hermitBindingExpr :: HermitBinding -> Maybe CoreExpr
hermitBindingExpr = hermitBindingSiteExpr . snd
{-# INLINE hermitBindingExpr #-}

------------------------------------------------------------------------

-- | A class of contexts that can have HERMIT bindings added to them.
class AddBindings c where
  -- | Add a complete set of parrallel bindings to the context.
  --   (Parallel bindings occur in recursive let bindings and case alternatives.)
  --   This can also be used for solitary bindings (e.g. lambdas).
  --   Bindings are added in parallel sets to help with shadowing issues.
  addHermitBindings :: [(Var,HermitBindingSite)] -> c -> c

-- | Here the bindings are just discarded.
instance AddBindings (SnocPath crumb) where
  addHermitBindings :: [(Var,HermitBindingSite)] -> SnocPath crumb -> SnocPath crumb
  addHermitBindings _ = id

-------------------------------------------

-- | Add a single binding to the context.
addHermitBinding  :: AddBindings c => Var -> HermitBindingSite -> c -> c
addHermitBinding v bd = addHermitBindings [(v,bd)]
{-# INLINE addHermitBinding #-}

-- | Add all bindings in a binding group to a context.
addBindingGroup :: AddBindings c => CoreBind -> c -> c
addBindingGroup (NonRec v e) = addHermitBinding  v (NONREC e)
addBindingGroup (Rec ies)    = addHermitBindings [ (i, REC e) | (i,e) <- ies ]
{-# INLINE addBindingGroup #-}

-- | Add a wildcard binding for a specific case alternative.
addCaseWildBinding :: AddBindings c => (Id,CoreExpr,CoreAlt) -> c -> c
addCaseWildBinding (i,e,(con,vs,_)) = addHermitBinding i (CASEWILD e (con,vs))
{-# INLINE addCaseWildBinding #-}

-- | Add a lambda bound variable to a context.
--   All that is known is the variable, which may shadow something.
--   If so, we don't worry about that here, it is instead checked during inlining.
addLambdaBinding :: AddBindings c => Var -> c -> c
addLambdaBinding v = addHermitBinding v LAM
{-# INLINE addLambdaBinding #-}

-- | Add the variables bound by a 'DataCon' in a case.
--   They are all bound at the same depth.
addAltBindings :: AddBindings c => [Var] -> c -> c
addAltBindings vs = addHermitBindings [ (v, CASEALT) | v <- vs ]
{-# INLINE addAltBindings #-}

-- | Add a universally quantified type variable to a context.
addForallBinding :: AddBindings c => TyVar -> c -> c
addForallBinding v = addHermitBinding v FORALL
{-# INLINE addForallBinding #-}

------------------------------------------------------------------------

-- | A class of contexts from which HERMIT bindings can be retrieved.
class ReadBindings c where
  hermitBindings :: c -> Map Var HermitBinding

-- | Lookup the binding for a variable in a context.
lookupHermitBinding :: ReadBindings c => Var -> c -> Maybe HermitBinding
lookupHermitBinding v = lookup v . hermitBindings
{-# INLINE lookupHermitBinding #-}

-- | List all the variables bound in a context.
boundVars :: ReadBindings c => c -> [Var]
boundVars = keys . hermitBindings
{-# INLINE boundVars #-}

-- | Determine if a variable is bound in a context.
boundIn :: ReadBindings c => Var -> c -> Bool
boundIn i c = i `elem` boundVars c
{-# INLINE boundIn #-}

-- | List all variables bound in the context that match the given name.
findBoundVars :: ReadBindings c => TH.Name -> c -> [Var]
findBoundVars nm = filter (cmpTHName2Var nm) . boundVars
{-# INLINE findBoundVars #-}

------------------------------------------------------------------------

-- | A class of contexts that store GHC rewrite rules.
class HasCoreRules c where
  hermitCoreRules :: c -> [CoreRule]

------------------------------------------------------------------------

-- | A class of contexts that store the Global Reader Environment.
class HasGlobalRdrEnv c where
  hermitGlobalRdrEnv :: c -> GlobalRdrEnv

------------------------------------------------------------------------

-- | The HERMIT context, containing all bindings in scope and the current location in the AST.
--   The bindings here are lazy by choice, so that we can avoid the cost
--   of building the context if we never use it.
data HermitC = HermitC
        { hermitC_bindings       :: Map Var HermitBinding   -- ^ All (important) bindings in scope.
        , hermitC_depth          :: BindingDepth            -- ^ The depth of the bindings.
        , hermitC_path           :: AbsolutePath Crumb      -- ^ The 'AbsolutePath' to the current node from the root.
        , hermitC_globalRdrEnv   :: GlobalRdrEnv            -- ^ The top-level lexical environment.
        , hermitC_coreRules      :: [CoreRule]              -- ^ GHC rewrite RULES.
        }

------------------------------------------------------------------------

-- | Create the initial HERMIT 'HermitC' by providing a 'ModGuts'.
initHermitC :: ModGuts -> HermitC
initHermitC modGuts = HermitC
                        { hermitC_bindings      = empty
                        , hermitC_depth         = 0
                        , hermitC_path          = mempty
                        , hermitC_globalRdrEnv  = mg_rdr_env modGuts
                        , hermitC_coreRules     = mg_rules modGuts ++ other_rules
                        }

    where other_rules :: [CoreRule]
          other_rules = mg_binds modGuts >>= bindToIdExprs >>= (idCoreRules . fst)
          {-# INLINE other_rules #-}
{-# INLINE initHermitC #-}

------------------------------------------------------------------------

-- | Retrieve the 'AbsolutePath' to the current node, from the HERMIT context.
instance ReadPath HermitC Crumb where
  absPath :: HermitC -> AbsolutePath Crumb
  absPath = hermitC_path
  {-# INLINE absPath #-}

-- | Extend the 'AbsolutePath' stored in the HERMIT context.
instance ExtendPath HermitC Crumb where
  (@@) :: HermitC -> Crumb -> HermitC
  c @@ n = c { hermitC_path = hermitC_path c @@ n }
  {-# INLINE (@@) #-}

------------------------------------------------------------------------

instance AddBindings HermitC where
  addHermitBindings :: [(Var,HermitBindingSite)] -> HermitC -> HermitC
  addHermitBindings vbs c = let nextDepth = succ (hermitC_depth c)
                                vhbs      = [ (v, (nextDepth,b)) | (v,b) <- vbs ]
                             in c { hermitC_bindings = fromList vhbs `union` hermitC_bindings c
                                  , hermitC_depth    = nextDepth
                                  }
  {-# INLINE addHermitBindings #-}

------------------------------------------------------------------------

instance ReadBindings HermitC where
  hermitBindings :: HermitC -> Map Var HermitBinding
  hermitBindings = hermitC_bindings
  {-# INLINE hermitBindings #-}

------------------------------------------------------------------------

instance HasCoreRules HermitC where
  hermitCoreRules :: HermitC -> [CoreRule]
  hermitCoreRules = hermitC_coreRules
  {-# INLINE hermitCoreRules #-}

------------------------------------------------------------------------

instance HasGlobalRdrEnv HermitC where
  hermitGlobalRdrEnv :: HermitC -> GlobalRdrEnv
  hermitGlobalRdrEnv = hermitC_globalRdrEnv
  {-# INLINE hermitGlobalRdrEnv #-}

------------------------------------------------------------------------
