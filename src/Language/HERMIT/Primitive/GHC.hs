module Language.HERMIT.Primitive.GHC where

import GhcPlugins

import Control.Applicative

import Language.KURE

import Language.HERMIT.HermitKure
import Language.HERMIT.External

------------------------------------------------------------------------

externals :: [External]
externals = map (.+ GHC)
         [ external "let-subst" (promoteR letSubstR)
                [ "Let substitution [via GHC]"]
         , external "freevars" (promoteT freeIdsQuery)
                [ "List the free variables in this expression [via GHC]" ]
         , external "deshadow-binds" (promoteR deShadowBindsR)
                [ "Deshadow a program [via GHC]" ]
         ]

------------------------------------------------------------------------

letSubstR :: RewriteH CoreExpr
letSubstR = rewrite $ \ c exp -> case exp of
      (Let (NonRec b be) e)
         | isId b    -> do
                let sub = extendSubst emptySubst b be
                return $ substExpr (text "letSubstR") sub e
      (Let (NonRec b (Type bty)) e)
         | isTyVar b -> do
                let sub = extendTvSubst emptySubst b bty
                return $ substExpr (text "letSubstR") sub e
      _ -> fail "LetSubst failed. Expr is not a (non-recursive) Let."

------------------------------------------------------------------------

-- output a list of all free variables in the Expr.
freeIdsQuery :: TranslateH CoreExpr String
freeIdsQuery = (("FreeVars are: " ++) . show . map (showSDoc.ppr)) <$> freeIdsT

freeIdsT :: TranslateH CoreExpr [Id]
freeIdsT = liftT freeIds

-- note: exprFreeIds is only value-level free variables
freeIds :: CoreExpr -> [Id]
freeIds  = uniqSetToList . exprFreeVars

------------------------------------------------------------------------

-- | [from GHC documentation] De-shadowing the program is sometimes a useful pre-pass.
-- It can be done simply by running over the bindings with an empty substitution,
-- becuase substitution returns a result that has no-shadowing guaranteed.
--
-- (Actually, within a single /type/ there might still be shadowing, because
-- 'substTy' is a no-op for the empty substitution, but that's probably OK.)
deShadowBindsR :: RewriteH CoreProgram
deShadowBindsR = liftT deShadowBinds

------------------------------------------------------------------------