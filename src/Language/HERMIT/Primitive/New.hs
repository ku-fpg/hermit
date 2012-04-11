{-# LANGUAGE TypeFamilies, FlexibleInstances #-}

-- Placeholder for new prims
module Language.HERMIT.Primitive.New where

import GhcPlugins
import qualified Data.Map as Map

import Language.HERMIT.Types
import Language.HERMIT.KURE
import Language.HERMIT.HermitEnv as Env

beta_reduce :: Rewrite CoreExpr
beta_reduce = rewrite $ \ (Context c e) -> case e of
        (App (Lam v e1) e2) -> return (Let (NonRec v e2) e1)
        _ -> fail $ "beta_reduce failed"
