module Language.HERMIT.Context
       (
         -- * HERMIT Bindings
         HermitBinding(..)
       , hermitBindingDepth
         -- * The HERMIT Context
       , Context
       , initContext
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
        | CASE Int CoreExpr (AltCon,[Id]) -- ^ For case wildcard binders. First expr points to scrutinee,
                                          --   second to AltCon (which can be converted to Constructor or Literal).

-- | Get the depth of a binding.
hermitBindingDepth :: HermitBinding -> Int
hermitBindingDepth (LAM d)      = d
hermitBindingDepth (BIND d _ _) = d
hermitBindingDepth (CASE d _ _) = d

------------------------------------------------------------------------

-- | The HERMIT context, containing all bindings in scope and the current location in the AST.
--   The bindings here are lazy by choice, so that we can avoid the cost
--   of building the context if we never use it.
data Context = Context
        { hermitBindings :: Map Id HermitBinding    -- ^ All (important) bindings in scope.
        , hermitDepth    :: Int                     -- ^ The depth of the bindings.
        , hermitPath     :: AbsolutePath            -- ^ The 'AbsolutePath' to the current node from the root.
        , hermitModGuts  :: ModGuts                 -- ^ The 'ModGuts' of the current module.
        }

------------------------------------------------------------------------

-- | The HERMIT context stores an 'AbsolutePath' to the current node in the tree.
instance PathContext Context where
  contextPath = hermitPath

-- | Create the initial HERMIT 'Context' by providing a 'ModGuts'.
initContext :: ModGuts -> Context
initContext modGuts = Context empty 0 rootAbsPath modGuts

-- | Update the context by extending the stored 'AbsolutePath' to a child.
(@@) :: Context -> Int -> Context
(@@) env n = env { hermitPath = extendAbsPath n (hermitPath env) }

-- | Add all bindings in a binding group to the 'Context'.
addBinding :: CoreBind -> Context -> Context
addBinding (NonRec n e) env
        = env { hermitBindings = insert n (BIND next_depth False e) (hermitBindings env)
              , hermitDepth    = next_depth
              }
  where
        next_depth = succ (hermitDepth env)
addBinding (Rec bds) env
        = env { hermitBindings = bds_env `union` hermitBindings env
              , hermitDepth    = next_depth
              }
  where
        next_depth = succ (hermitDepth env)
        -- notice how all recursive binding in a binding group are at the same depth.
        bds_env    = fromList
                   [ (b,BIND next_depth True e)
                   | (b,e) <- bds
                   ]

-- | Add the bindings for a specific case alternative.
addCaseBinding :: (Id,CoreExpr,CoreAlt) -> Context -> Context
addCaseBinding (n,e,(ac,is,_)) env
        = env { hermitBindings = insert n (CASE next_depth e (ac,is)) (hermitBindings env)
              , hermitDepth    = next_depth
              }
  where
        next_depth = succ (hermitDepth env)

-- | Add a binding that you know nothing about, except that it may shadow something.
-- If so, do not worry about it here, just remember the binding and the depth.
-- When we want to inline a value from the environment,
-- we then check to see what is free in the inlinee, and see
-- if any of the frees will stop the validity of the inlining.
addLambdaBinding :: Id -> Context -> Context
addLambdaBinding n env
        = env { hermitBindings = insert n (LAM next_depth) (hermitBindings env)
              , hermitDepth    = next_depth
              }
  where
        next_depth = succ (hermitDepth env)

-- | Add the Ids bound by a DataCon in a case. Like lambda bindings,
-- in that we know nothing about them, but all bound at the same depth,
-- so we cannot just fold addLambdaBinding over the list.
addAltBindings :: [Id] -> Context -> Context
addAltBindings ns env
        = env { hermitBindings = foldr (\n bds -> insert n (LAM next_depth) bds) (hermitBindings env) ns
              , hermitDepth    = next_depth
              }
  where next_depth = succ (hermitDepth env)

-- | Lookup the binding for an identifier in a 'Context'.
lookupHermitBinding :: Id -> Context -> Maybe HermitBinding
lookupHermitBinding n env = lookup n (hermitBindings env)

-- | List all the identifiers bound in the 'Context'.
listBindings :: Context -> [Id]
listBindings = keys . hermitBindings

-- | Determine if an identifier is bound in the 'Context'.
boundIn :: Id -> Context -> Bool
boundIn i c = i `elem` listBindings c

------------------------------------------------------------------------
