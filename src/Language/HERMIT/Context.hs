{-# LANGUAGE InstanceSigs #-}

module Language.HERMIT.Context
       ( -- * The HERMIT Context
         HermitC
       , initHermitC
         -- ** Adding to the Context
       , addAltBindings
       , addBinding
       , addCaseBinding
       , addLambdaBinding
         -- ** Reading from the Context
       , hermitBindings
       , hermitDepth
       , hermitPath
       , hermitModGuts
       , lookupHermitBinding
       , boundVars
       , boundIn
       , findBoundVars
         -- ** Bindings
       , HermitBinding(..)
       , hermitBindingDepth
) where

import Prelude hiding (lookup)
import GhcPlugins hiding (empty)
import Data.Map hiding (map, foldr, filter)
import qualified Language.Haskell.TH as TH

import Language.HERMIT.GHC

import Language.KURE

------------------------------------------------------------------------

-- | HERMIT\'s representation of variable bindings.
data HermitBinding
        = BIND Int Bool CoreExpr  -- ^ Binding depth, whether it is recursive, and the bound value
                                  --   (which cannot be inlined without checking for scoping issues).
        | LAM Int                 -- ^ For a lambda binding you only know the depth.
        | CASE Int CoreExpr (AltCon,[Id]) -- ^ For case wildcard binders. We store both the scrutinised expression,
                                          --   and the case alternative 'AltCon' (which can be converted to Constructor or Literal) and identifiers.

-- | Get the depth of a binding.
hermitBindingDepth :: HermitBinding -> Int
hermitBindingDepth (LAM d)      = d
hermitBindingDepth (BIND d _ _) = d
hermitBindingDepth (CASE d _ _) = d

------------------------------------------------------------------------

-- | The HERMIT context, containing all bindings in scope and the current location in the AST.
--   The bindings here are lazy by choice, so that we can avoid the cost
--   of building the context if we never use it.
data HermitC = HermitC
        { hermitBindings :: Map Var HermitBinding   -- ^ All (important) bindings in scope.
        , hermitDepth    :: Int                     -- ^ The depth of the bindings.
        , hermitPath     :: AbsolutePath            -- ^ The 'AbsolutePath' to the current node from the root.
        , hermitModGuts  :: ModGuts                 -- ^ The 'ModGuts' of the current module.
        }

------------------------------------------------------------------------

-- | The HERMIT context stores an 'AbsolutePath' to the current node in the tree.
instance PathContext HermitC where
  absPath :: HermitC -> AbsolutePath
  absPath = hermitPath

  (@@) :: HermitC -> Int -> HermitC
  c @@ n = c { hermitPath = hermitPath c @@ n }


-- | Create the initial HERMIT 'HermitC' by providing a 'ModGuts'.
initHermitC :: ModGuts -> HermitC
initHermitC modGuts = HermitC empty 0 rootAbsPath modGuts

------------------------------------------------------------------------

-- | Add all bindings in a binding group to a context.
addBinding :: CoreBind -> HermitC -> HermitC
addBinding corebind c = let nextDepth = succ (hermitDepth c)
                            hbds      = hermitBindings c
                            newBds    = case corebind of
                                          NonRec v e  -> insert v (BIND nextDepth False e) hbds
                                          Rec bds     -> hbds `union` fromList [ (b, BIND nextDepth True e) | (b,e) <- bds ]
                                                         -- Notice how all recursive binding in a binding group are at the same depth.
                        in c { hermitBindings = newBds
                             , hermitDepth    = nextDepth
                             }

-- | Add the bindings for a specific case alternative.
addCaseBinding :: (Id,CoreExpr,CoreAlt) -> HermitC -> HermitC
addCaseBinding (v,e,(con,vs,_)) c = let nextDepth = succ (hermitDepth c)
                                     in c { hermitBindings = insert v (CASE nextDepth e (con,vs)) (hermitBindings c)
                                          , hermitDepth    = nextDepth
                                          }

-- | Add a lambda bound variable to a context.
--   All that is known is the variable, which may shadow something.
--   If so, we don't worry about that here, it is instead checked during inlining.
addLambdaBinding :: Var -> HermitC -> HermitC
addLambdaBinding v c = let nextDepth = succ (hermitDepth c)
                        in c { hermitBindings = insert v (LAM nextDepth) (hermitBindings c)
                             , hermitDepth    = nextDepth
                             }

-- | Add the variables bound by a 'DataCon' in a case. Like lambda bindings,
-- in that we know nothing about them, but all bound at the same depth,
-- so we cannot just fold 'addLambdaBinding' over the list.
addAltBindings :: [Var] -> HermitC -> HermitC
addAltBindings vs c = let nextDepth = succ (hermitDepth c)
                       in c { hermitBindings = foldr (\ v bds -> insert v (LAM nextDepth) bds) (hermitBindings c) vs
                            , hermitDepth    = nextDepth
                            }
-- TODO: Is treating case-alternative bindings as lambda bindings okay?
--       There's no issues with lambda bindings being sequential and case-alternative bindings being in parallel?

------------------------------------------------------------------------

-- | Lookup the binding for a variable in a context.
lookupHermitBinding :: Var -> HermitC -> Maybe HermitBinding
lookupHermitBinding n env = lookup n (hermitBindings env)

-- | List all the variables bound in a context.
boundVars :: HermitC -> [Var]
boundVars = keys . hermitBindings

-- | Determine if a variable is bound in a context.
boundIn :: Var -> HermitC -> Bool
boundIn i c = i `elem` boundVars c

------------------------------------------------------------------------

-- | List all variables bound in the context that match the given name.
findBoundVars :: TH.Name -> HermitC -> [Var]
findBoundVars nm = filter (cmpTHName2Var nm) . boundVars

------------------------------------------------------------------------
