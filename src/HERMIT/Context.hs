{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, InstanceSigs #-}

module HERMIT.Context
       ( -- * HERMIT Contexts
         -- ** Path Synonyms
         AbsolutePathH
       , LocalPathH
         -- ** The Standard Context
       , HermitC
       , initHermitC
         -- ** Bindings
       , HermitBindingSite(..)
       , BindingDepth
       , HermitBinding
       , hermitBindingSiteExpr
       , hermitBindingSummary
       , hermitBindingExpr
         -- ** Adding bindings to contexts
       , AddBindings(..)
       , addBindingGroup
       , addDefBinding
       , addDefBindingsExcept
       , addLambdaBinding
       , addAltBindings
       , addCaseWildBinding
       , addForallBinding
         -- ** Reading bindings from the context
       , BoundVars(..)
       , boundIn
       , findBoundVars
       , ReadBindings(..)
       , lookupHermitBinding
       , lookupHermitBindingDepth
       , lookupHermitBindingSite
         -- ** Accessing the Global Reader Environment from the context
       , HasGlobalRdrEnv(..)
         -- ** Accessing GHC rewrite rules from the context
       , HasCoreRules(..)
) where

import Prelude hiding (lookup)

import Control.Monad (liftM)

import Data.Monoid (mempty)
import Data.Map hiding (map, foldr, filter)

import qualified Language.Haskell.TH as TH

import Language.KURE
import Language.KURE.ExtendableContext

import HERMIT.Core
import HERMIT.GHC hiding (empty)

------------------------------------------------------------------------

-- | The depth of a binding.  Used, for example, to detect shadowing when inlining.
type BindingDepth = Int


-- | HERMIT\'s representation of variable bindings.
--   Bound expressions cannot be inlined without checking for shadowing issues (using the depth information).
data HermitBindingSite = LAM                               -- ^ A lambda-bound variable.
                       | NONREC CoreExpr                   -- ^ A non-recursive binding of an expression.
                       | REC CoreExpr                      -- ^ A recursive binding that does not depend on the current expression (i.e. we're not in the binding group of that binding).
                       | SELFREC                           -- ^ A recursive binding of a superexpression of the current node (i.e. we're in the RHS of that binding).
                       | MUTUALREC CoreExpr                -- ^ A recursive binding that is mutually recursive with the binding under consideration (i.e. we're in another definition in the same recursive binding group.).
                       | CASEALT                           -- ^ A variable bound in a case alternative.
                       | CASEWILD CoreExpr (AltCon,[Var])  -- ^ A case wildcard binder.  We store both the scrutinised expression, and the case alternative 'AltCon' and variables.
                       | FORALL                            -- ^ A universally quantified type variable.

type HermitBinding = (BindingDepth, HermitBindingSite)

-- | Retrieve the expression in a 'HermitBindingSite', if there is one.
hermitBindingSiteExpr :: HermitBindingSite -> KureM CoreExpr
hermitBindingSiteExpr b = case b of
                            LAM          -> fail "variable is lambda-bound, not bound to an expression."
                            NONREC e     -> return e
                            REC e        -> return e
                            MUTUALREC e  -> return e
                            SELFREC      -> fail "identifier recursively refers to the expression under consideration."
                            CASEALT      -> fail "variable is bound in a case alternative, not bound to an expression."
                            CASEWILD e _ -> return e
                            FORALL       -> fail "variable is a universally quantified type variable."

hermitBindingSummary :: HermitBinding -> String
hermitBindingSummary (d,b) = show d ++ "$" ++ case b of
                            LAM          -> "LAM"
                            NONREC {}    -> "NONREC"
                            REC {}       -> "REC"
                            MUTUALREC {} -> "MUTUALREC"
                            SELFREC {}   -> "SELFREC"
                            CASEALT      -> "CASEALT"
                            CASEWILD {}  -> "CASEWILD"
                            FORALL       -> "FORALL"

-- | Retrieve the expression in a 'HermitBinding', if there is one.
hermitBindingExpr :: HermitBinding -> KureM CoreExpr
hermitBindingExpr = hermitBindingSiteExpr . snd

------------------------------------------------------------------------

-- | A class of contexts that can have HERMIT bindings added to them.
class AddBindings c where
  -- | Add a complete set of parrallel bindings to the context.
  --   (Parallel bindings occur in recursive let bindings and case alternatives.)
  --   This can also be used for solitary bindings (e.g. lambdas).
  --   Bindings are added in parallel sets to help with shadowing issues.
  addHermitBindings :: [(Var,HermitBindingSite)] -> c -> c

-- | The bindings are just discarded.
instance AddBindings (SnocPath crumb) where
  addHermitBindings :: [(Var,HermitBindingSite)] -> SnocPath crumb -> SnocPath crumb
  addHermitBindings _ = id

-- | The bindings are added to the base context and the extra context.
instance (AddBindings c, AddBindings e) => AddBindings (ExtendContext c e) where
  addHermitBindings :: [(Var,HermitBindingSite)] -> ExtendContext c e -> ExtendContext c e
  addHermitBindings bnds c = c
                              { baseContext  = addHermitBindings bnds (baseContext c)
                              , extraContext = addHermitBindings bnds (extraContext c)
                              }

-------------------------------------------

-- | Add a single binding to the context.
addHermitBinding  :: AddBindings c => Var -> HermitBindingSite -> c -> c
addHermitBinding v bd = addHermitBindings [(v,bd)]

-- | Add all bindings in a binding group to a context.
addBindingGroup :: AddBindings c => CoreBind -> c -> c
addBindingGroup (NonRec v e) = addHermitBinding  v (NONREC e)
addBindingGroup (Rec ies)    = addHermitBindings [ (i, REC e) | (i,e) <- ies ]

-- | Add the binding for a recursive definition currently under examination.
--   Note that because the expression may later be modified, the context only records the identifier, not the expression.
addDefBinding :: AddBindings c => Id -> c -> c
addDefBinding i = addHermitBinding i SELFREC

-- | Add a list of recursive bindings to the context, except the nth binding in the list.
--   The idea is to exclude the definition being descended into.
addDefBindingsExcept :: AddBindings c => Int -> [(Id,CoreExpr)] -> c -> c
addDefBindingsExcept n ies = addHermitBindings [ (i, MUTUALREC e) | (m,(i,e)) <- zip [0..] ies, m /= n ]

-- | Add a wildcard binding for a specific case alternative.
addCaseWildBinding :: AddBindings c => (Id,CoreExpr,CoreAlt) -> c -> c
addCaseWildBinding (i,e,(con,vs,_)) = addHermitBinding i (CASEWILD e (con,vs))

-- | Add a lambda bound variable to a context.
--   All that is known is the variable, which may shadow something.
--   If so, we don't worry about that here, it is instead checked during inlining.
addLambdaBinding :: AddBindings c => Var -> c -> c
addLambdaBinding v = addHermitBinding v LAM

-- | Add the variables bound by a 'DataCon' in a case.
--   They are all bound at the same depth.
addAltBindings :: AddBindings c => [Var] -> c -> c
addAltBindings vs = addHermitBindings [ (v, CASEALT) | v <- vs ]

-- | Add a universally quantified type variable to a context.
addForallBinding :: AddBindings c => TyVar -> c -> c
addForallBinding v = addHermitBinding v FORALL

------------------------------------------------------------------------

-- | A class of contexts that stores the set of variables in scope that have been bound during the traversal.
class BoundVars c where
  boundVars :: c -> VarSet

instance BoundVars VarSet where
  boundVars :: VarSet -> VarSet
  boundVars = id

-- | List all variables bound in the context that match the given name.
findBoundVars :: BoundVars c => TH.Name -> c -> VarSet
findBoundVars nm = filterVarSet (cmpTHName2Var nm) . boundVars


-- | A class of contexts from which HERMIT bindings can be retrieved.
class BoundVars c => ReadBindings c where
  hermitDepth    :: c -> BindingDepth
  hermitBindings :: c -> Map Var HermitBinding

-- | Determine if a variable is bound in a context.
boundIn :: ReadBindings c => Var -> c -> Bool
boundIn i c = i `member` hermitBindings c

-- | Lookup the binding for a variable in a context.
lookupHermitBinding :: (ReadBindings c, Monad m) => Var -> c -> m HermitBinding
lookupHermitBinding v = maybe (fail "binding not found in HERMIT context.") return . lookup v . hermitBindings

-- | Lookup the depth of a variable's binding in a context.
lookupHermitBindingDepth :: (ReadBindings c, Monad m) => Var -> c -> m BindingDepth
lookupHermitBindingDepth v = liftM fst . lookupHermitBinding v

-- | Lookup the binding for a variable in a context, ensuring it was bound at the specified depth.
lookupHermitBindingSite :: (ReadBindings c, Monad m) => Var -> BindingDepth -> c -> m HermitBindingSite
lookupHermitBindingSite v depth c = do (d,bnd) <- lookupHermitBinding v c
                                       guardMsg (d == depth) "lookupHermitBinding succeeded, but depth does not match.  The variable has probably been shadowed."
                                       return bnd

------------------------------------------------------------------------

-- | A class of contexts that store GHC rewrite rules.
class HasCoreRules c where
  hermitCoreRules :: c -> [CoreRule]

instance HasCoreRules [CoreRule] where
  hermitCoreRules :: [CoreRule] -> [CoreRule]
  hermitCoreRules = id

------------------------------------------------------------------------

-- | A class of contexts that store the Global Reader Environment.
class HasGlobalRdrEnv c where
  hermitGlobalRdrEnv :: c -> GlobalRdrEnv

instance HasGlobalRdrEnv GlobalRdrEnv where
  hermitGlobalRdrEnv :: GlobalRdrEnv -> GlobalRdrEnv
  hermitGlobalRdrEnv = id

------------------------------------------------------------------------

type AbsolutePathH = AbsolutePath Crumb
type LocalPathH = LocalPath Crumb

-- | The HERMIT context, containing all bindings in scope and the current location in the AST.
--   The bindings here are lazy by choice, so that we can avoid the cost
--   of building the context if we never use it.
data HermitC = HermitC
        { hermitC_bindings       :: Map Var HermitBinding   -- ^ All (important) bindings in scope.
        , hermitC_depth          :: BindingDepth            -- ^ The depth of the most recent bindings.
        , hermitC_path           :: AbsolutePathH           -- ^ The 'AbsolutePath' to the current node from the root.
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
          other_rules = mg_binds modGuts >>= bindToVarExprs >>= (idCoreRules . fst)

------------------------------------------------------------------------

-- | Retrieve the 'AbsolutePath' to the current node, from the HERMIT context.
instance ReadPath HermitC Crumb where
  absPath :: HermitC -> AbsolutePath Crumb
  absPath = hermitC_path

-- | Extend the 'AbsolutePath' stored in the HERMIT context.
instance ExtendPath HermitC Crumb where
  (@@) :: HermitC -> Crumb -> HermitC
  c @@ n = c { hermitC_path = hermitC_path c @@ n }

------------------------------------------------------------------------

instance AddBindings HermitC where
  addHermitBindings :: [(Var,HermitBindingSite)] -> HermitC -> HermitC
  addHermitBindings vbs c = let nextDepth = succ (hermitC_depth c)
                                vhbs      = [ (v, (nextDepth,b)) | (v,b) <- vbs ]
                             in c { hermitC_bindings = fromList vhbs `union` hermitC_bindings c
                                  , hermitC_depth    = nextDepth
                                  }

------------------------------------------------------------------------

instance BoundVars HermitC where
  boundVars :: HermitC -> VarSet
  boundVars =  mkVarSet . keys . hermitC_bindings

instance ReadBindings HermitC where
  hermitDepth :: HermitC -> BindingDepth
  hermitDepth = hermitC_depth

  hermitBindings :: HermitC -> Map Var HermitBinding
  hermitBindings = hermitC_bindings

------------------------------------------------------------------------

instance HasCoreRules HermitC where
  hermitCoreRules :: HermitC -> [CoreRule]
  hermitCoreRules = hermitC_coreRules

------------------------------------------------------------------------

instance HasGlobalRdrEnv HermitC where
  hermitGlobalRdrEnv :: HermitC -> GlobalRdrEnv
  hermitGlobalRdrEnv = hermitC_globalRdrEnv

------------------------------------------------------------------------
