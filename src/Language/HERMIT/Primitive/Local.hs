-- Andre Santos' Local Transformations (Ch 3 in his dissertation)
module Language.HERMIT.Primitive.Local where

import GhcPlugins

import Data.List (nub)
import Control.Applicative
import Control.Monad (guard)

import Language.KURE

import Language.HERMIT.HermitKure
import Language.HERMIT.HermitEnv
import Language.HERMIT.HermitMonad
import Language.HERMIT.External

import Language.HERMIT.Primitive.GHC

import qualified Language.HERMIT.Primitive.Local.Case as Case
import qualified Language.HERMIT.Primitive.Local.Let as Let

import qualified Language.Haskell.TH as TH

------------------------------------------------------------------------------

externals :: [External]
externals = map (.+ Local) $
         [ external "beta-reduce" (promoteR beta_reduce)
                     [ "((\\ v -> E1) E2) ==> let v = E2 in E1, fails otherwise"
                     , "this form of beta reduction is safe if E2 is an arbitrary"
                     , "expression (won't duplicate work)" ] .+ Bash
         , external "beta-expand" (promoteR beta_expand)
                     [ "(let v = E1 in E2) ==> (\\ v -> E2) E1, fails otherwise" ]
         , external "dead-code" (promoteR dce)
                     [ "dead code elimination removes a let."
                     , "(let v = E1 in E2) ==> E2, if v is not free in E2, fails otherwise"
                     , "condition: let is not-recursive" ] .+ Bash
         , external "eta-reduce" (promoteR eta_reduce)
                     [ "(\\ v -> E1 v) ==> E1, fails otherwise" ]
         , external "eta-expand" (promoteR . eta_expand)
                     [ "'eta-expand v' performs E1 ==> (\\ v -> E1 v), fails otherwise" ]
         ]
         ++ Let.externals
         ++ Case.externals

------------------------------------------------------------------------------

beta_reduce :: RewriteH CoreExpr
beta_reduce = liftMT $ \ e -> case e of
        App (Lam v e1) e2 -> return $ Let (NonRec v e2) e1
        _ -> fail "beta_reduce failed. Not applied to an App."

beta_expand :: RewriteH CoreExpr
beta_expand = liftMT $ \ e -> case e of
        Let (NonRec v e2) e1 -> return $ App (Lam v e1) e2
        _ -> fail "beta_expand failed. Not applied to a NonRec Let."

------------------------------------------------------------------------------

eta_reduce :: RewriteH CoreExpr
eta_reduce = liftMT $ \ e -> case e of
      Lam v1 (App f (Var v2)) -> do guardFail (v1 == v2) "eta_reduce failed, variables are not equal."
                                    guardFail (v1 `notElem` freeIds f) $ "eta_reduce failed. " ++ showSDoc (ppr v1) ++
                                                                         "is free in the function being applied."
                                    return f
      _                       -> fail "eta_reduce failed"

eta_expand :: TH.Name -> RewriteH CoreExpr
eta_expand nm = liftMT $ \ e -> case splitAppTy_maybe (exprType e) of
                                  Nothing           -> fail "eta-expand failed (expression is not an App)"
                                  Just (_ , arg_ty) -> do v1 <- newVarH nm arg_ty
                                                          return $ Lam v1 (App e (Var v1))

------------------------------------------------------------------------------

-- dead code elimination removes a let.
-- (let v = E1 in E2) => E2, if v is not free in E2
dce :: RewriteH CoreExpr
dce = liftMT $ \ e -> case e of
        Let (NonRec n e1) e2 | n `notElem` freeIds e2 -> return e2
                             | otherwise              -> fail "DCE: no dead code"
        _ -> fail "DCE: not applied to a NonRec Let."

------------------------------------------------------------------------------

-- NOT IN USE.  Use the GHC version instead.

-- notice that we pass in the (empty) initial Hermit environment.
-- Notice the use of "mtryT".  This ensures all failures are converted to []s (the unit of the monoid).
freeVarsExpr :: CoreExpr -> HermitM [Id]
freeVarsExpr = fmap nub . apply (crushtdT $ promoteT freeVarT) initHermitEnv . ExprCore
  where
    freeVarT :: TranslateH CoreExpr [Id]
    freeVarT = do (c,Var n) <- exposeT
                  guard (not (n `boundInHermit` c))
                  return [n]

------------------------------------------------------------------------------
