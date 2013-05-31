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
       , HermitBinding(..)
       , BindingDepth
       , hermitBindingDepth
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
data HermitBinding
        = BIND BindingDepth Bool CoreExpr                -- ^ Depth of the binding, whether it is recursive, and the bound expression
                                                         --   (which cannot be inlined without checking for shadowing issues).
        | DISEMBODIED BindingDepth                       -- ^ A binding with no bound expression, such as a lambda variable or case alternative variable.
                                                         --   This constructor is also used for case alternative variable bindings, as they likewise lack a bound expression.
        | CASEWILD BindingDepth CoreExpr (AltCon,[Var])  -- ^ For case wildcard binders, we store both the scrutinised expression,
                                                         --   and the case alternative 'AltCon' (which can be converted to Constructor or Literal) and variables.

-- | Get the depth of a binding.
hermitBindingDepth :: HermitBinding -> BindingDepth
hermitBindingDepth (DISEMBODIED d)  = d
hermitBindingDepth (BIND d _ _)     = d
hermitBindingDepth (CASEWILD d _ _) = d
{-# INLINE hermitBindingDepth #-}

------------------------------------------------------------------------

class BindingContext c where
  -- | Add a complete set of parrallel bindings to the context.
  --   (Parallel bindings occur in recursive let bindings and case alternatives.)
  --   This can also be used for solitary bindings (e.g. lambdas).
  --   A typical instance of this function would increment the current depth in the context, and provide the updated depth for use in constructing the bindings.
  --   It is because of this depth maintainence that we take the bindings in parallel sets.
  addHermitBindings :: (BindingDepth -> [(Var,HermitBinding)]) -> c -> c

-------------------------------------------

-- | Add a single binding to the context.
addHermitBinding  :: BindingContext c => (BindingDepth -> (Var,HermitBinding)) -> c -> c
addHermitBinding f = addHermitBindings (\ d -> [f d])
{-# INLINE addHermitBinding #-}

-- | Add all bindings in a binding group to a context.
addBindingGroup :: BindingContext c => CoreBind -> c -> c
addBindingGroup (NonRec v e) = addHermitBinding  $ \ depth -> (v, BIND depth False e)
addBindingGroup (Rec ies)    = addHermitBindings $ \ depth -> [ (i, BIND depth True e) | (i,e) <- ies ]
{-# INLINE addBindingGroup #-}

-- | Add a wildcard binding for a specific case alternative.
addCaseWildBinding :: BindingContext c => (Id,CoreExpr,CoreAlt) -> c -> c
addCaseWildBinding (i,e,(con,vs,_)) = addHermitBinding $ \ depth -> (i, CASEWILD depth e (con,vs))
{-# INLINE addCaseWildBinding #-}

-- | Add a lambda bound variable to a context.
--   All that is known is the variable, which may shadow something.
--   If so, we don't worry about that here, it is instead checked during inlining.
addLambdaBinding :: BindingContext c => Var -> c -> c
addLambdaBinding v =  addHermitBinding $ \ depth -> (v, DISEMBODIED depth)
{-# INLINE addLambdaBinding #-}

-- | Add the variables bound by a 'DataCon' in a case.
--   They are all bound at the same depth.
addAltBindings :: BindingContext c => [Var] -> c -> c
addAltBindings vs = addHermitBindings $ \ depth -> [ (v, DISEMBODIED depth) | v <- vs ]
{-# INLINE addAltBindings #-}

-- | Add a universally quantified type variable to a context.
addForallBinding :: BindingContext c => TyVar -> c -> c
addForallBinding v = addHermitBinding $ \ depth -> (v, DISEMBODIED depth)
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
  addHermitBindings :: (BindingDepth -> [(Var,HermitBinding)]) -> HermitC -> HermitC
  addHermitBindings f c = let nextDepth = succ (hermitC_depth c)
                              vbs       = f nextDepth
                           in
                              c { hermitC_bindings = fromList vbs `union` hermitC_bindings c
                                , hermitC_depth    = nextDepth
                                }
  {-# INLINE addHermitBindings #-}

------------------------------------------------------------------------
