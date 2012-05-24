module Language.HERMIT.Primitive.GHC where

import GhcPlugins

import Data.List (nub)
import Control.Applicative

import Language.KURE

import Language.HERMIT.HermitKure
import Language.HERMIT.HermitEnv
import Language.HERMIT.HermitMonad
import Language.HERMIT.External

import qualified Language.Haskell.TH as TH

externals :: [External]
externals = map (.+ GHC)
         [ external "let-subst" (promoteR letSubstR)
                [ "Let substitution [via GHC]"]
         , external "freevars" (promoteT freeIdsQuery)
                [ "List the free variables in this expression." ]
         ]

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


-- output a list of all free variables in the Expr.
freeIdsQuery :: TranslateH CoreExpr String
freeIdsQuery = (("FreeVars are: " ++) . show . map (showSDoc.ppr)) <$> freeIdsT

freeIdsT :: TranslateH CoreExpr [Id]
freeIdsT = liftT freeIds

-- note: exprFreeIds is only value-level free variables
freeIds :: CoreExpr -> [Id]
freeIds  = uniqSetToList . exprFreeVars
