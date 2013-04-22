module Language.HERMIT.Primitive.Unfold
    ( externals
    , cleanupUnfoldR
    , rememberR
    , unfoldR
    , unfoldStashR
    ) where

import GhcPlugins hiding (empty)
import Control.Applicative
import Control.Arrow
import Control.Monad

import qualified Language.Haskell.TH as TH

import Language.HERMIT.Primitive.Common
import Language.HERMIT.Primitive.GHC hiding (externals)
import Language.HERMIT.Primitive.Inline hiding (externals)
import Language.HERMIT.Primitive.Local hiding (externals)

import Language.HERMIT.Core
import Language.HERMIT.Kure
import Language.HERMIT.Monad
import Language.HERMIT.External
import Language.HERMIT.GHC

import Prelude hiding (exp)

------------------------------------------------------------------------

externals :: [External]
externals =
    [ external "cleanup-unfold" (promoteExprR cleanupUnfoldR :: RewriteH Core)
        [ "Clean up immediately nested fully-applied lambdas, from the bottom up"] .+ Deep
    , external "remember" rememberR
        ["Remember the current binding, allowing it to be folded/unfolded in the future."] .+ Context
    , external "unfold" (promoteExprR . unfoldStashR)
        ["Unfold a remembered definition."] .+ Deep .+ Context
    , external "unfold" (promoteExprR . unfoldR :: TH.Name -> RewriteH Core)
        [ "Inline a definition, and apply the arguments; traditional unfold"] .+ Deep .+ Context
    , external "unfold-rule" ((\ nm -> promoteExprR (rule nm >>> cleanupUnfoldR)) :: String -> RewriteH Core)
        [ "Apply a named GHC rule" ] .+ Deep .+ Context -- TODO: does not work with rules with no arguments
    ]

------------------------------------------------------------------------

-- | cleanupUnfoldR cleans a unfold operation
--  (for example, an inline or rule application)
-- It is used at the level of the top-redex.
cleanupUnfoldR :: RewriteH CoreExpr
cleanupUnfoldR = betaReducePlus >>> safeLetSubstPlusR

unfoldR :: TH.Name -> RewriteH CoreExpr
unfoldR nm = translate $ \ env e0 -> do
        let n = appCount e0
        let sub :: RewriteH Core
            sub = pathR (replicate n 0) (promoteR $ inlineName nm)

            sub2 :: RewriteH CoreExpr
            sub2 = extractR sub

        e1 <- apply sub2 env e0

        -- only cleanup if 1 or more arguments
        if n > 0 then apply cleanupUnfoldR env e1
                 else return e1

-- NOTE: Using a Rewrite because of the way the Kernel is set up.
--       This is a temperary hack until we work out the best way to structure the Kernel.

-- | Stash a binding with a name for later use.
-- Allows us to look at past definitions.
rememberR :: String -> RewriteH Core
rememberR label = sideEffectR $ \ _ core ->
  case core of
    DefCore def           -> saveDef label def
    BindCore (NonRec i e) -> saveDef label (Def i e)
    _                     -> fail "remember: not a binding"

-- | Stash a binding with a name for later use.
-- Allows us to look at past definitions.
-- rememberR :: String -> TranslateH Core ()
-- rememberR label = contextfreeT $ \ core ->
--     case core of
--         DefCore def -> saveDef label def
--         BindCore (NonRec i e) -> saveDef label (Def i e)
--         _           -> fail "remember: not a binding"

-- | Apply a stashed definition (like inline, but looks in stash instead of context).
unfoldStashR :: String -> RewriteH CoreExpr
unfoldStashR label = setFailMsg "Inlining stashed definition failed: " $
                   withPatFailMsg (wrongExprForm "Var v") $
                   do (c, Var v) <- exposeT
                      constT $ do Def i rhs <- lookupDef label
                                  if idName i == idName v -- TODO: Is there a reason we're not just using equality on Id?
                                    then ifM (all (inScope c) <$> apply freeVarsT c rhs)
                                             (return rhs)
                                             (fail "some free variables in stashed definition are no longer in scope.")
                                    else fail $ "stashed definition applies to " ++ var2String i ++ " not " ++ var2String v

