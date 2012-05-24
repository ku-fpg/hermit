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
externals =
         [ external "let-subst" (promoteR letSubstR)
                [ "Let substitution [via GHC]"]
            .+ GHC
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
