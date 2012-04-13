{-# LANGUAGE TypeFamilies, FlexibleInstances #-}

-- Placeholder for new prims
module Language.HERMIT.Primitive.New where

import GhcPlugins hiding ((<>))
import qualified Data.Map as Map

import Language.HERMIT.Types
import Language.HERMIT.External
import Language.HERMIT.KURE
import Language.HERMIT.HermitEnv as Env

import qualified Language.Haskell.TH as TH


externals :: External
externals = external "beta-reduce" (promoteR beta_reduce)
                [ "((\\ v -> E1) E2) ==> let v = E2 in E1, fails otherwise"
                ]
         <> external "beta-expand" (promoteR beta_expand)
                [ "(let v = E1 in E2) ==> (\\ v -> E2) E1, fails otherwise"
                ]
         <> external "eta-reduce" (promoteR eta_reduce)
                [ "(\\ v -> E1 v) ==> E1, fails otherwise"
                ]
         <> external "eta-expand" (promoteR . eta_expand)
                [ "'ext-expand v' performs E1 ==> (\\ v -> E1 v), fails otherwise"
                ]
         <> external "let-intro" (promoteR . eta_expand)
                [ "'let-intro v' performs E1 ==> (let v = E1 in v), fails otherwise"
                ]
         <> external "subst" (promoteR subst)
                [ "(let v = E1 in E2) ==> E2[E1/v], fails otherwise"
                , "condition: let is not-recursive"
                ]
         <> external "var" (\ nm -> promoteR . var nm . extractR)
                [ "'var <v>' applies a rewrite to all <v>"
                ]

beta_reduce :: Rewrite CoreExpr
beta_reduce = rewrite $ \ (Context c e) -> case e of
        (App (Lam v e1) e2) -> return (Let (NonRec v e2) e1)
        _ -> fail $ "beta_reduce failed"

beta_expand :: Rewrite CoreExpr
beta_expand = rewrite $ \ (Context c e) -> case e of
        (Let (NonRec v e2) e1) -> return (App (Lam v e1) e2)
        _ -> fail $ "beta_expand failed"


eta_reduce :: Rewrite CoreExpr
eta_reduce = rewrite $ \ (Context c e) -> case e of
        (App (Lam v1 e1) (Var v2))
                -- TODO: check that v1/v2 is not free in e1
                | v1 == v2 -> return e1
        _ -> fail $ "eta_reduce failed"

eta_expand :: TH.Name -> Rewrite CoreExpr
eta_expand _ = rewrite $ \ (Context c e) -> case e of
        _ -> fail $ "eta_expand failed (NOT implemented)"

let_intro :: TH.Name -> Rewrite CoreExpr
let_intro _ = rewrite $ \ (Context c e) -> case e of
        _ -> fail $ "let_intro failed (NOT implemented)"

-- | 'subst' assumes that the input expression is of the form 'let v = E1 in E2'.
subst :: Rewrite CoreExpr
subst = rewrite $ \ (Context c e) -> case e of
        _ -> fail $ "subst failed (NOT implemented)"


var :: TH.Name -> Rewrite CoreExpr -> Rewrite CoreExpr
var _ n = idR -- bottomupR (varR (\ n -> ()) ?

