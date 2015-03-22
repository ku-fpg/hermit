{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}

module HERMIT.Context
    ( -- * HERMIT Contexts
      -- ** Path Synonyms
      AbsolutePathH
    , LocalPathH
      -- ** The Standard Context
    , HermitC
    , topLevelHermitC
      -- ** Bindings
    , HermitBindingSite(..)
    , BindingDepth
    , HermitBinding
    , hbDepth
    , hbSite
    , hbPath
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
    , addCaseBinderBinding
    , addForallBinding
      -- ** Reading bindings from the context
    , BoundVars(..)
    , boundIn
    , findBoundVars
    , ReadBindings(..)
    , lookupHermitBinding
    , lookupHermitBindingDepth
    , lookupHermitBindingSite
    , inScope
      -- ** Accessing GHC rewrite rules from the context
    , HasCoreRules(..)
      -- ** Accessing temporary lemmas in scope
    , LemmaContext(..)
      -- ** An empty Context
    , HasEmptyContext(..)
    ) where

import Prelude hiding (lookup)

import Control.Monad (liftM)

import Data.Monoid (mempty)
import Data.Map hiding (map, foldr, filter)

import Language.KURE
import Language.KURE.ExtendableContext

import HERMIT.Core
import HERMIT.GHC hiding (empty)
import HERMIT.Lemma

------------------------------------------------------------------------

-- | The depth of a binding.  Used, for example, to detect shadowing when inlining.
type BindingDepth = Int

-- | HERMIT\'s representation of variable bindings.
--   Bound expressions cannot be inlined without checking for shadowing issues (using the depth information).
data HermitBindingSite = LAM                                -- ^ A lambda-bound variable.
                       | NONREC CoreExpr                    -- ^ A non-recursive binding of an expression.
                       | REC CoreExpr                       -- ^ A recursive binding that does not depend on the current expression (i.e. we're not in the binding group of that binding).
                       | SELFREC                            -- ^ A recursive binding of a superexpression of the current node (i.e. we're in the RHS of that binding).
                       | MUTUALREC CoreExpr                 -- ^ A recursive binding that is mutually recursive with the binding under consideration (i.e. we're in another definition in the same recursive binding group.).
                       | CASEALT                            -- ^ A variable bound in a case alternative.
                       | CASEBINDER CoreExpr (AltCon,[Var]) -- ^ A case binder.  We store both the scrutinised expression, and the case alternative 'AltCon' and variables.
                       | FORALL                             -- ^ A universally quantified type variable.
                       | TOPLEVEL CoreExpr                  -- ^ A special case.  When we're focussed on ModGuts, we treat all top-level bindings as being in scope at depth 0.

data HermitBinding = HB { hbDepth :: BindingDepth
                        , hbSite :: HermitBindingSite
                        , hbPath :: AbsolutePathH
                        }

-- | Retrieve the expression in a 'HermitBindingSite', if there is one.
hermitBindingSiteExpr :: HermitBindingSite -> KureM CoreExpr
hermitBindingSiteExpr b = case b of
                            LAM            -> fail "variable is lambda-bound, not bound to an expression."
                            NONREC e       -> return e
                            REC e          -> return e
                            MUTUALREC e    -> return e
                            SELFREC        -> fail "identifier recursively refers to the expression under consideration."
                            CASEALT        -> fail "variable is bound in a case alternative, not bound to an expression."
                            CASEBINDER e _ -> return e
                            FORALL         -> fail "variable is a universally quantified type variable."
                            TOPLEVEL e     -> return e

hermitBindingSummary :: HermitBinding -> String
hermitBindingSummary b = show (hbDepth b) ++ "$" ++ case hbSite b of
                            LAM            -> "LAM"
                            NONREC {}      -> "NONREC"
                            REC {}         -> "REC"
                            MUTUALREC {}   -> "MUTUALREC"
                            SELFREC {}     -> "SELFREC"
                            CASEALT        -> "CASEALT"
                            CASEBINDER {}  -> "CASEBINDER"
                            FORALL         -> "FORALL"
                            TOPLEVEL {}    -> "TOPLEVEL"

-- | Retrieve the expression in a 'HermitBinding', if there is one.
hermitBindingExpr :: HermitBinding -> KureM CoreExpr
hermitBindingExpr = hermitBindingSiteExpr . hbSite

------------------------------------------------------------------------

-- | A class of contexts that can have HERMIT bindings added to them.
class AddBindings c where
  -- | Add a complete set of parrallel bindings to the context.
  --   (Parallel bindings occur in recursive let bindings and case alternatives.)
  --   This can also be used for solitary bindings (e.g. lambdas).
  --   Bindings are added in parallel sets to help with shadowing issues.
  addHermitBindings :: [(Var,HermitBindingSite,AbsolutePathH)] -> c -> c

-- | The bindings are just discarded.
instance AddBindings (SnocPath crumb) where
  addHermitBindings :: [(Var,HermitBindingSite,AbsolutePathH)] -> SnocPath crumb -> SnocPath crumb
  addHermitBindings _ = id

instance ReadPath c Crumb => ReadPath (ExtendContext c e) Crumb where
  absPath = absPath . baseContext

-- | The bindings are added to the base context and the extra context.
instance (AddBindings c, AddBindings e) => AddBindings (ExtendContext c e) where
  addHermitBindings :: [(Var,HermitBindingSite,AbsolutePathH)] -> ExtendContext c e -> ExtendContext c e
  addHermitBindings bnds c = c
                              { baseContext  = addHermitBindings bnds (baseContext c)
                              , extraContext = addHermitBindings bnds (extraContext c)
                              }

-------------------------------------------

-- | Add all bindings in a binding group to a context.
addBindingGroup :: (AddBindings c, ReadPath c Crumb) => CoreBind -> c -> c
addBindingGroup (NonRec v e) c = addHermitBindings [(v,NONREC e,absPath c @@ Let_Bind)] c
addBindingGroup (Rec ies)    c = addHermitBindings [ (i, REC e, absPath c @@ Let_Bind) | (i,e) <- ies ] c

-- | Add the binding for a recursive definition currently under examination.
--   Note that because the expression may later be modified, the context only records the identifier, not the expression.
addDefBinding :: (AddBindings c, ReadPath c Crumb) => Id -> c -> c
addDefBinding i c = addHermitBindings [(i,SELFREC,absPath c @@ Def_Id)] c

-- | Add a list of recursive bindings to the context, except the nth binding in the list.
--   The idea is to exclude the definition being descended into.
addDefBindingsExcept :: (AddBindings c, ReadPath c Crumb) => Int -> [(Id,CoreExpr)] -> c -> c
addDefBindingsExcept n ies c = addHermitBindings [ (i, MUTUALREC e, absPath c @@ Rec_Def m) | (m,(i,e)) <- zip [0..] ies, m /= n ] c

-- | Add the case binder for a specific case alternative.
addCaseBinderBinding :: (AddBindings c, ReadPath c Crumb) => (Id,CoreExpr,CoreAlt) -> c -> c
addCaseBinderBinding (i,e,(con,vs,_)) c = addHermitBindings [(i,CASEBINDER e (con,vs),absPath c @@ Case_Binder)] c

-- | Add a lambda bound variable to a context.
--   All that is known is the variable, which may shadow something.
--   If so, we don't worry about that here, it is instead checked during inlining.
addLambdaBinding :: (AddBindings c, ReadPath c Crumb) => Var -> c -> c
addLambdaBinding v c = addHermitBindings [(v,LAM,absPath c @@ Lam_Var)] c

-- | Add the variables bound by a 'DataCon' in a case.
--   They are all bound at the same depth.
addAltBindings :: (AddBindings c, ReadPath c Crumb) => [Var] -> c -> c
addAltBindings vs c = addHermitBindings [ (v, CASEALT, absPath c @@ Alt_Var i) | (v,i) <- zip vs [1..] ] c

-- | Add a universally quantified type variable to a context.
addForallBinding :: (AddBindings c, ReadPath c Crumb) => TyVar -> c -> c
addForallBinding v c = addHermitBindings [(v,FORALL,absPath c @@ ForAllTy_Var)] c

------------------------------------------------------------------------

-- | A class of contexts that stores the set of variables in scope that have been bound during the traversal.
class BoundVars c where
  boundVars :: c -> VarSet

instance BoundVars VarSet where
  boundVars :: VarSet -> VarSet
  boundVars = id

-- | List all variables bound in the context that match the given predicate.
findBoundVars :: BoundVars c => (Var -> Bool) -> c -> VarSet
findBoundVars p = filterVarSet p . boundVars

-- | A class of contexts from which HERMIT bindings can be retrieved.
class BoundVars c => ReadBindings c where
  hermitDepth    :: c -> BindingDepth
  hermitBindings :: c -> Map Var HermitBinding

-- | Determine if a variable is bound in a context.
boundIn :: ReadBindings c => Var -> c -> Bool
boundIn i c = i `member` hermitBindings c

-- | Determine whether a variable is in scope.
inScope :: BoundVars c => c -> Var -> Bool
inScope c v = not (isDeadBinder v || (isLocalVar v && (v `notElemVarSet` boundVars c)))
-- Used in Dictionary.Inline and Dictionary.Fold to check if variables are in scope.

-- | Lookup the binding for a variable in a context.
lookupHermitBinding :: (ReadBindings c, Monad m) => Var -> c -> m HermitBinding
lookupHermitBinding v = maybe (fail "binding not found in HERMIT context.") return . lookup v . hermitBindings

-- | Lookup the depth of a variable's binding in a context.
lookupHermitBindingDepth :: (ReadBindings c, Monad m) => Var -> c -> m BindingDepth
lookupHermitBindingDepth v = liftM hbDepth . lookupHermitBinding v

-- | Lookup the binding for a variable in a context, ensuring it was bound at the specified depth.
lookupHermitBindingSite :: (ReadBindings c, Monad m) => Var -> BindingDepth -> c -> m HermitBindingSite
lookupHermitBindingSite v depth c = do HB d bnd _ <- lookupHermitBinding v c
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

-- | A class of contexts that provide an empty context.
class HasEmptyContext c where
  setEmptyContext :: c -> c

------------------------------------------------------------------------

-- | A class of contexts that can store local Lemmas as we descend past implications.
class LemmaContext c where
    addAntecedent :: LemmaName -> Lemma -> c -> c
    getAntecedents :: c -> Lemmas

instance LemmaContext c => LemmaContext (ExtendContext c e) where
    addAntecedent nm l ec = extendContext (extraContext ec)
                                          (addAntecedent nm l $ baseContext ec)
    getAntecedents = getAntecedents . baseContext

------------------------------------------------------------------------

type AbsolutePathH = AbsolutePath Crumb
type LocalPathH = LocalPath Crumb

-- | The HERMIT context, containing all bindings in scope and the current location in the AST.
--   The bindings here are lazy by choice, so that we can avoid the cost
--   of building the context if we never use it.
data HermitC = HermitC
    { hermitC_bindings  :: Map Var HermitBinding -- ^ All (local to this module) bindings in scope.
    , hermitC_depth     :: BindingDepth          -- ^ The depth of the most recent bindings.
    , hermitC_path      :: AbsolutePathH         -- ^ The 'AbsolutePath' to the current node from the root.
    , hermitC_specRules :: [CoreRule]            -- ^ In-scope GHC RULES found in IdInfos.
    , hermitC_lemmas    :: Lemmas                -- ^ Local lemmas as we pass implications in a proof.
    }

------------------------------------------------------------------------

-- | The |HermitC| empty context has an initial depth of 0, an empty path, and no bindings nor rules.
instance HasEmptyContext HermitC where
  setEmptyContext :: HermitC -> HermitC
  setEmptyContext c = c
                 { hermitC_bindings      = empty
                 , hermitC_depth         = 0
                 , hermitC_path          = mempty
                 , hermitC_specRules     = []
                 , hermitC_lemmas        = empty
                 }

-- | A special HERMIT context intended for use only when focussed on ModGuts.
--   All top-level bindings are considered to be in scope at depth 0.
topLevelHermitC :: ModGuts -> HermitC
topLevelHermitC mg = let ies = concatMap bindToVarExprs (mg_binds mg)
                      in HermitC
                       { hermitC_bindings      = fromList [ (i , HB 0 (TOPLEVEL e) mempty) | (i,e) <- ies ]
                       , hermitC_depth         = 0
                       , hermitC_path          = mempty
                       , hermitC_specRules     = concatMap (idCoreRules . fst) ies
                       , hermitC_lemmas        = empty
                       }

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
  addHermitBindings :: [(Var,HermitBindingSite,AbsolutePathH)] -> HermitC -> HermitC
  addHermitBindings vbs c =
    let nextDepth = succ (hermitC_depth c)
        vhbs      = [ (v, HB nextDepth b p) | (v,b,p) <- vbs ]
    in c { hermitC_bindings  = fromList vhbs `union` hermitC_bindings c
         , hermitC_depth     = nextDepth
         , hermitC_specRules = concat [ idCoreRules i | (i,_,_) <- vbs, isId i ] ++ hermitC_specRules c
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
  hermitCoreRules = hermitC_specRules

------------------------------------------------------------------------

instance LemmaContext HermitC where
    addAntecedent :: LemmaName -> Lemma -> HermitC -> HermitC
    addAntecedent nm l c = c { hermitC_lemmas = insert nm l (hermitC_lemmas c) }

    getAntecedents :: HermitC -> Lemmas
    getAntecedents = hermitC_lemmas
