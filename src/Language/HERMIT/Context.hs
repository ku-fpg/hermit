{-# LANGUAGE InstanceSigs, ConstraintKinds #-}

module Language.HERMIT.Context
       ( -- * HERMIT Contexts
         -- ** The Standard Context
         HermitC
       , initHermitC
       , hermitC_globalRdrEnv
       , hermitC_coreRules
         -- ** Context for 'Type' Traversals
       , TypeC
       , initTypeC
       , typePath
       , forallTyVars
       , addForallTyVar
         -- ** Bindings
       , HermitBinding(..)
       , BindingDepth
       , hermitBindingDepth
         -- ** Contexts that track Bindings
       , BindingContext
         -- *** Adding Bindings
       , addBindingGroup
       , addLambdaBinding
       , addAltBindings
       , addCaseBinding
         -- *** Querying Bindings
       , hermitBindings
       , lookupHermitBinding
       , boundVars
       , boundIn
       , findBoundVars
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
        = BIND BindingDepth Bool CoreExpr            -- ^ Depth of the binding, whether it is recursive, and the bound expression
                                                     --   (which cannot be inlined without checking for shadowing issues).
        | LAM BindingDepth                           -- ^ A lambda binding has no bound expression, you only know the depth.
                                                     --   This constructor is also used for case alternative variable bindings, as they likewise lack a bound expression.
        | CASE BindingDepth CoreExpr (AltCon,[Var])  -- ^ For case wildcard binders, we store both the scrutinised expression,
                                                     --   and the case alternative 'AltCon' (which can be converted to Constructor or Literal) and variables.

-- | Get the depth of a binding.
hermitBindingDepth :: HermitBinding -> BindingDepth
hermitBindingDepth (LAM d)      = d
hermitBindingDepth (BIND d _ _) = d
hermitBindingDepth (CASE d _ _) = d
{-# INLINE hermitBindingDepth #-}

------------------------------------------------------------------------

class BindingContext c where
  hermitBindings    :: c -> Map Var HermitBinding
  addHermitBinding  :: Var -> HermitBinding -> c -> c
  currentDepth      :: c -> BindingDepth
  incDepth          :: c -> c

-------------------------------------------

-- | Lookup the binding for a variable in a context.
lookupHermitBinding :: BindingContext c => Var -> c -> Maybe HermitBinding
lookupHermitBinding v = lookup v . hermitBindings
{-# INLINE lookupHermitBinding #-}

-- | List all the variables bound in a context.
boundVars :: BindingContext c => c -> [Var]
boundVars = keys . hermitBindings
{-# INLINE boundVars #-}

-- | Determine if a variable is bound in a context.
boundIn :: BindingContext c => Var -> c -> Bool
boundIn i c = i `elem` boundVars c
{-# INLINE boundIn #-}

-- | List all variables bound in the context that match the given name.
findBoundVars :: BindingContext c => TH.Name -> c -> [Var]
findBoundVars nm = filter (cmpTHName2Var nm) . boundVars
{-# INLINE findBoundVars #-}

-------------------------------------------

nextDepth :: BindingContext c => c -> (BindingDepth,c)
nextDepth c = let c' = incDepth c
               in (currentDepth c', c')
{-# INLINE nextDepth #-}

-------------------------------------------

addHermitBindings :: BindingContext c => [(Var,HermitBinding)] -> c -> c
addHermitBindings vbs c = foldr (uncurry addHermitBinding) c vbs
{-# INLINE addHermitBindings #-}

-- | Add all bindings in a binding group to a context.
addBindingGroup :: BindingContext c => CoreBind -> c -> c
addBindingGroup bnd c = let (depth,c')  = nextDepth c
                            newBnds = case bnd of
                                        NonRec v e  -> [ (v, BIND depth False e) ]
                                        Rec ies     -> [ (i, BIND depth True e) | (i,e) <- ies ]
                                                       -- All recursive binding in a binding group are at the same depth.
                         in addHermitBindings newBnds c'
{-# INLINE addBindingGroup #-}

-- | Add a wildcard binding for a specific case alternative.
addCaseBinding :: BindingContext c => (Id,CoreExpr,CoreAlt) -> c -> c
addCaseBinding (i,e,(con,vs,_)) c = let (depth,c') = nextDepth c
                                     in addHermitBindings [(i,CASE depth e (con,vs))] c'
{-# INLINE addCaseBinding #-}

-- | Add a lambda bound variable to a context.
--   All that is known is the variable, which may shadow something.
--   If so, we don't worry about that here, it is instead checked during inlining.
addLambdaBinding :: BindingContext c => Var -> c -> c
addLambdaBinding v c = let (depth,c') = nextDepth c
                         in addHermitBindings [(v,LAM depth)] c'
{-# INLINE addLambdaBinding #-}

-- | Add the variables bound by a 'DataCon' in a case. Like lambda bindings,
-- in that we know nothing about them, but all bound at the same depth,
-- so we cannot just fold 'addLambdaBinding' over the list.
addAltBindings :: BindingContext c => [Var] -> c -> c
addAltBindings vs c = let (depth,c') = nextDepth c
                       in addHermitBindings [ (v,LAM depth) | v <- vs ] c'
{-# INLINE addAltBindings #-}

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
  hermitBindings :: HermitC -> Map Var HermitBinding
  hermitBindings = hermitC_bindings
  {-# INLINE hermitBindings #-}

  addHermitBinding :: Var -> HermitBinding -> HermitC -> HermitC
  addHermitBinding v hb c = c { hermitC_bindings = insert v hb (hermitC_bindings c) }
  {-# INLINE addHermitBinding #-}

  currentDepth :: HermitC -> BindingDepth
  currentDepth = hermitC_depth
  {-# INLINE currentDepth #-}

  incDepth :: HermitC -> HermitC
  incDepth c = c { hermitC_depth = succ (hermitC_depth c) }
  {-# INLINE incDepth #-}

------------------------------------------------------------------------

-- Type Traversals


-- | A context for 'Type' traversals.
data TypeC = TypeC { forallTyVars :: [TyVar]        -- ^ All universally quantified type variables that are in scope,
                                                    --   and have been declared within the type being traversed.
                   , typePath     :: AbsolutePath   -- ^ The 'AbsolutePath' to the current node from the root of the 'Type'.
                   }


-- | The HERMIT context stores an 'AbsolutePath' to the current node in the tree.
instance PathContext TypeC where
  absPath :: TypeC -> AbsolutePath
  absPath = typePath
  {-# INLINE absPath #-}

  (@@) :: TypeC -> Int -> TypeC
  c @@ n = c { typePath = typePath c @@ n }
  {-# INLINE (@@) #-}


-- | Create an initial (empty) context for 'Type' traversals.
initTypeC :: TypeC
initTypeC = TypeC { forallTyVars = []
                  , typePath     = rootAbsPath
                  }
{-# INLINE initTypeC #-}

-- | Add a universally quantified type variable to a type context.
addForallTyVar :: TyVar -> TypeC -> TypeC
addForallTyVar v c = c { forallTyVars = v : forallTyVars c }
{-# INLINE addForallTyVar #-}

------------------------------------------------------------------------
