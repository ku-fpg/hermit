{-# LANGUAGE InstanceSigs, ConstraintKinds #-}

module Language.HERMIT.Context
       ( -- * HERMIT Contexts
         -- ** The Standard Context
         HermitC
       , initHermitC
       , hermitC_bindings
       , hermitC_globalRdrEnv
       , hermitC_coreRules
       , lookupHermitBinding
       , boundVars
       , boundIn
       , findBoundVars
         -- ** Bindings
       , HermitBindingSite(..)
       , BindingDepth
       , HermitBinding
       , hermitBindingSiteExpr
       , hermitBindingExpr
         -- ** Contexts that track Bindings
       , BindingContext
       , addBindingGroup
       , addLambdaBinding
       , addAltBindings
       , addCaseWildBinding
       , addForallBinding
) where

import Prelude hiding (lookup)
import GhcPlugins hiding (empty)
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

class BindingContext c where
  -- | Add a complete set of parrallel bindings to the context.
  --   (Parallel bindings occur in recursive let bindings and case alternatives.)
  --   This can also be used for solitary bindings (e.g. lambdas).
  --   Bindings are added in parallel sets to help with shadowing issues.
  addHermitBindings :: [(Var,HermitBindingSite)] -> c -> c

-------------------------------------------

-- | Add a single binding to the context.
addHermitBinding  :: BindingContext c => Var -> HermitBindingSite -> c -> c
addHermitBinding v bd = addHermitBindings [(v,bd)]
{-# INLINE addHermitBinding #-}

-- | Add all bindings in a binding group to a context.
addBindingGroup :: BindingContext c => CoreBind -> c -> c
addBindingGroup (NonRec v e) = addHermitBinding  v (NONREC e)
addBindingGroup (Rec ies)    = addHermitBindings [ (i, REC e) | (i,e) <- ies ]
{-# INLINE addBindingGroup #-}

-- | Add a wildcard binding for a specific case alternative.
addCaseWildBinding :: BindingContext c => (Id,CoreExpr,CoreAlt) -> c -> c
addCaseWildBinding (i,e,(con,vs,_)) = addHermitBinding i (CASEWILD e (con,vs))
{-# INLINE addCaseWildBinding #-}

-- | Add a lambda bound variable to a context.
--   All that is known is the variable, which may shadow something.
--   If so, we don't worry about that here, it is instead checked during inlining.
addLambdaBinding :: BindingContext c => Var -> c -> c
addLambdaBinding v = addHermitBinding v LAM
{-# INLINE addLambdaBinding #-}

-- | Add the variables bound by a 'DataCon' in a case.
--   They are all bound at the same depth.
addAltBindings :: BindingContext c => [Var] -> c -> c
addAltBindings vs = addHermitBindings [ (v, CASEALT) | v <- vs ]
{-# INLINE addAltBindings #-}

-- | Add a universally quantified type variable to a context.
addForallBinding :: BindingContext c => TyVar -> c -> c
addForallBinding v = addHermitBinding v FORALL
{-# INLINE addForallBinding #-}

------------------------------------------------------------------------

-- | The HERMIT context, containing all bindings in scope and the current location in the AST.
--   The bindings here are lazy by choice, so that we can avoid the cost
--   of building the context if we never use it.
data HermitC = HermitC
        { hermitC_bindings       :: Map Var HermitBinding   -- ^ All (important) bindings in scope.
        , hermitC_depth          :: BindingDepth            -- ^ The depth of the bindings.
        , hermitC_path           :: AbsolutePath            -- ^ The 'AbsolutePath' to the current node from the root.
        , hermitC_globalRdrEnv   :: GlobalRdrEnv            -- ^ The top-level lexical environment.
        , hermitC_coreRules      :: [CoreRule]              -- ^ GHC rewrite RULES.
        }

------------------------------------------------------------------------

-- | Lookup the binding for a variable in a context.
lookupHermitBinding :: Var -> HermitC -> Maybe HermitBinding
lookupHermitBinding v = lookup v . hermitC_bindings
{-# INLINE lookupHermitBinding #-}

-- | List all the variables bound in a context.
boundVars :: HermitC -> [Var]
boundVars = keys . hermitC_bindings
{-# INLINE boundVars #-}

-- | Determine if a variable is bound in a context.
boundIn :: Var -> HermitC -> Bool
boundIn i c = i `elem` boundVars c
{-# INLINE boundIn #-}

-- | List all variables bound in the context that match the given name.
findBoundVars :: TH.Name -> HermitC -> [Var]
findBoundVars nm = filter (cmpTHName2Var nm) . boundVars
{-# INLINE findBoundVars #-}

------------------------------------------------------------------------

-- | The HERMIT context stores an 'AbsolutePath' to the current node in the tree.
instance PathContext HermitC where
  absPath :: HermitC -> AbsolutePath
  absPath = hermitC_path
  {-# INLINE absPath #-}

  (@@) :: HermitC -> Int -> HermitC
  c @@ n = c { hermitC_path = hermitC_path c @@ n }
  {-# INLINE (@@) #-}

-- | Create the initial HERMIT 'HermitC' by providing a 'ModGuts'.
initHermitC :: ModGuts -> HermitC
initHermitC modGuts = HermitC
                        { hermitC_bindings      = empty
                        , hermitC_depth         = 0
                        , hermitC_path          = rootAbsPath
                        , hermitC_globalRdrEnv  = mg_rdr_env modGuts
                        , hermitC_coreRules     = mg_rules modGuts ++ other_rules
                        }

    where other_rules :: [CoreRule]
          other_rules = mg_binds modGuts >>= bindToIdExprs >>= (idCoreRules . fst)
          {-# INLINE other_rules #-}
{-# INLINE initHermitC #-}

------------------------------------------------------------------------

instance BindingContext HermitC where
  addHermitBindings :: [(Var,HermitBindingSite)] -> HermitC -> HermitC
  addHermitBindings vbs c = let nextDepth = succ (hermitC_depth c)
                                vhbs      = [ (v, (nextDepth,b)) | (v,b) <- vbs ]
                             in c { hermitC_bindings = fromList vhbs `union` hermitC_bindings c
                                  , hermitC_depth    = nextDepth
                                  }
  {-# INLINE addHermitBindings #-}

------------------------------------------------------------------------
