{-# LANGUAGE InstanceSigs #-}

module Language.HERMIT.Context
       (
         -- * HERMIT Bindings
         HermitBinding(..)
       , hermitBindingDepth
         -- * The HERMIT Context
       , HermitC
       , initHermitC
       , (@@)
       , addAltBindings
       , addBinding
       , addCaseBinding
       , addLambdaBinding
       , hermitBindings
       , hermitDepth
       , hermitPath
       , hermitModGuts
       , lookupHermitBinding
       , listBindings
       , boundIn
) where

import Prelude hiding (lookup)
import GhcPlugins hiding (empty)
import Data.Map hiding (map, foldr)

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
        { hermitBindings :: Map Id HermitBinding    -- ^ All (important) bindings in scope.
        , hermitDepth    :: Int                     -- ^ The depth of the bindings.
        , hermitPath     :: AbsolutePath            -- ^ The 'AbsolutePath' to the current node from the root.
        , hermitModGuts  :: ModGuts                 -- ^ The 'ModGuts' of the current module.
        }

------------------------------------------------------------------------

-- | The HERMIT context stores an 'AbsolutePath' to the current node in the tree.
instance PathContext HermitC where
  contextPath :: HermitC -> AbsolutePath
  contextPath = hermitPath

-- | Create the initial HERMIT 'HermitC' by providing a 'ModGuts'.
initHermitC :: ModGuts -> HermitC
initHermitC modGuts = HermitC empty 0 rootAbsPath modGuts

-- | Update the context by extending the stored 'AbsolutePath' to a child.
(@@) :: HermitC -> Int -> HermitC
(@@) c v = c { hermitPath = extendAbsPath v (hermitPath c) }

------------------------------------------------------------------------

-- | Add all bindings in a binding group to the 'HermitC'.
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

-- | Add a binding that you know nothing about, except that it may shadow something.
-- If so, do not worry about it here, just remember the binding and the depth.
-- When we want to inline a value from the environment,
-- we then check to see what is free in the inlinee, and see
-- if any of the frees will stop the validity of the inlining.
addLambdaBinding :: Id -> HermitC -> HermitC
addLambdaBinding v c = let nextDepth = succ (hermitDepth c)
                        in c { hermitBindings = insert v (LAM nextDepth) (hermitBindings c)
                             , hermitDepth    = nextDepth
                             }

-- | Add the identifiers bound by a 'DataCon' in a case. Like lambda bindings,
-- in that we know nothing about them, but all bound at the same depth,
-- so we cannot just fold addLambdaBinding over the list.
addAltBindings :: [Id] -> HermitC -> HermitC
addAltBindings vs c = let nextDepth = succ (hermitDepth c)
                       in c { hermitBindings = foldr (\ v bds -> insert v (LAM nextDepth) bds) (hermitBindings c) vs
                            , hermitDepth    = nextDepth
                            }

------------------------------------------------------------------------

-- | Lookup the binding for an identifier in a 'HermitC'.
lookupHermitBinding :: Id -> HermitC -> Maybe HermitBinding
lookupHermitBinding n env = lookup n (hermitBindings env)

-- | List all the identifiers bound in a 'HermitC'.
listBindings :: HermitC -> [Id]
listBindings = keys . hermitBindings

-- | Determine if an identifier is bound in the 'HermitC'.
boundIn :: Id -> HermitC -> Bool
boundIn i c = i `elem` listBindings c

------------------------------------------------------------------------
