{-# LANGUAGE TypeFamilies, FlexibleInstances #-}

-- module Language.HERMIT.HermitEnv where
module HermitEnv where

import GhcPlugins
import qualified Data.Map as Map

-- The bindings here are lazy by choice, so that we can avoid the cost
-- of building the environment, if we never use it.
data HermitEnv = HermitEnv
        { hermitBindings :: Map.Map Id HermitBinding    -- ^ all (important) bindings in scope
        , hermitDepth    :: Int                         -- ^ depth of bindings
        , hermitPath     :: ContextPath                 -- ^ path to the current node from the root.
        }

data HermitBinding
        = LAM                   -- all you know you have a lambda bound value Id **or type Id**.
                Int             -- depth
        | BIND                  -- you have something attached to this binding
                Int             -- depth
                Bool            -- recursive?
                (Expr Id)       -- Value (can not be inlined without checking for scoping issues)


-- | A list of node childen taken to get here. The head is the *last* branch.
newtype ContextPath = ContextPath [Int]

hermitBindingDepth :: HermitBinding -> Int

hermitBindingDepth (LAM d)  = d
hermitBindingDepth (BIND d _ _) = d

hermitBindingPath :: HermitEnv -> ContextPath
hermitBindingPath = hermitPath

(@@) :: HermitEnv -> Int -> HermitEnv
(@@) env n = env { hermitPath = case hermitPath env of
                                  ContextPath ns -> ContextPath (n : ns) }

-- A binding you know nothing about, except it may shadow something.
-- If so, do not worry about it here, just remember the binding a the depth.
-- When we want to inline a value from the environment,
-- we *then* check to see what is free in the inlinee, and see
-- if any of the frees will stop the validity of the inlining.

addHermitEnvLambdaBinding :: Id -> HermitEnv -> HermitEnv
addHermitEnvLambdaBinding n env
        = env { hermitBindings = Map.insert n (LAM next_depth) (hermitBindings env)
              , hermitDepth    = next_depth
              }
  where
        next_depth = succ (hermitDepth env)

addHermitBinding :: Bind Id -> HermitEnv -> HermitEnv
addHermitBinding (NonRec n e) env
        = env { hermitBindings = Map.insert n (BIND next_depth False e) (hermitBindings env)
              , hermitDepth    = next_depth
              }
  where
        next_depth = succ (hermitDepth env)
addHermitBinding (Rec bds) env
        = env { hermitBindings = Map.union bds_env (hermitBindings env)
              , hermitDepth    = next_depth
              }
  where
        next_depth = succ (hermitDepth env)
        -- notice how all recursive binding in a binding group are at the same depth.
        bds_env    = Map.fromList
                   [ (b,BIND next_depth True e)
                   | (b,e) <- bds
                   ]

lookupHermitBinding :: Id -> HermitEnv -> Maybe HermitBinding
lookupHermitBinding n env = Map.lookup n (hermitBindings env)

initHermitEnv :: HermitEnv
initHermitEnv = HermitEnv (Map.empty) 0 (ContextPath [])
