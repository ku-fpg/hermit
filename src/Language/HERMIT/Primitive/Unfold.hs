{-# LANGUAGE FlexibleContexts, ScopedTypeVariables, TupleSections, LambdaCase #-}
module Language.HERMIT.Primitive.Unfold
    ( externals
    , cleanupUnfoldR
    , rememberR
    , showStashT
    , unfoldR
    , unfoldPredR
    , unfoldNameR
    , unfoldAnyR
    , unfoldSaturatedR
    , unfoldStashR
    , specializeR
    ) where

import GhcPlugins hiding (empty)
import Control.Applicative
import Control.Arrow
import Control.Monad

import qualified Data.Map as Map
import Data.Set (toList)

import qualified Language.Haskell.TH as TH

import Language.HERMIT.PrettyPrinter.Common (DocH, PrettyH, TranslateDocH(..), PrettyC)

import Language.HERMIT.Primitive.Common
import Language.HERMIT.Primitive.GHC (rule,inScope,freeVarsT)
import Language.HERMIT.Primitive.Inline (inlineR)
import Language.HERMIT.Primitive.Local.Let (letSubstR)

import Language.HERMIT.Core
import Language.HERMIT.Context
import Language.HERMIT.Kure
import Language.HERMIT.Monad
import Language.HERMIT.External
import Language.HERMIT.GHC

import Prelude hiding (exp)

import qualified Text.PrettyPrint.MarkedHughesPJ as PP

------------------------------------------------------------------------

externals :: [External]
externals =
    [ external "cleanup-unfold" (promoteExprR cleanupUnfoldR :: RewriteH Core)
        [ "Clean up immediately nested fully-applied lambdas, from the bottom up" ] .+ Deep
    , external "remember" (rememberR :: Label -> RewriteH Core)
        [ "Remember the current binding, allowing it to be folded/unfolded in the future." ] .+ Context
    , external "unfold" (promoteExprR . unfoldStashR :: String -> RewriteH Core)
        [ "Unfold a remembered definition." ] .+ Deep .+ Context
    , external "unfold" (promoteExprR unfoldR :: RewriteH Core)
        [ "In application f x y z, unfold f." ] .+ Deep .+ Context
    , external "unfold" (promoteExprR . unfoldNameR :: TH.Name -> RewriteH Core)
        [ "Inline a definition, and apply the arguments; traditional unfold" ] .+ Deep .+ Context
    , external "unfold-saturated" (promoteExprR unfoldSaturatedR :: RewriteH Core)
        [ "Unfold a definition only if the function is fulled applied." ] .+ Deep .+ Context
    , external "specialize" (promoteExprR specializeR :: RewriteH Core)
        [ "Specialize an application to its type and coercion arguments." ] .+ Deep .+ Context
    , external "unfold-rule" ((\ nm -> promoteExprR (rule nm >>> cleanupUnfoldR)) :: String -> RewriteH Core)
        [ "Apply a named GHC rule" ] .+ Deep .+ Context .+ TODO -- TODO: does not work with rules with no arguments
    , external "show-remembered" (TranslateDocH showStashT :: TranslateDocH CoreTC)
        [ "Display all remembered definitions." ]
    ]

------------------------------------------------------------------------

-- | cleanupUnfoldR cleans a unfold operation
--  (for example, an inline or rule application)
-- It is used at the level of the top-redex.
-- Invariant: will not introduce let bindings
cleanupUnfoldR :: (AddBindings c, ExtendPath c Crumb, MonadCatch m) => Rewrite c m CoreExpr
cleanupUnfoldR = do
    (f, args) <- callT <+ arr (,[])
    let (vs, body) = collectBinders f
        lenargs = length args
        lenvs = length vs
        comp = compare lenargs lenvs
        body' = case comp of
                    LT -> mkCoreLams (drop lenargs vs) body
                    _  -> body
        bnds = zipWith NonRec vs args
    body'' <- andR (replicate (length bnds) letSubstR) <<< return (mkCoreLets bnds body')
    return $ case comp of
                GT -> mkCoreApps body'' $ drop lenvs args
                _  -> body''

-- | A more powerful 'inline'. Matches two cases:
--      Var ==> inlines
--      App ==> inlines the head of the function call for the app tree
unfoldR :: forall c. (ExtendPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
unfoldR = go >>> cleanupUnfoldR
    where go :: Rewrite c HermitM CoreExpr
          go = inlineR <+ appAllR go idR

unfoldPredR :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => (Id -> [CoreExpr] -> Bool) -> Rewrite c HermitM CoreExpr
unfoldPredR p = callPredT p >> unfoldR

unfoldNameR :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => TH.Name -> Rewrite c HermitM CoreExpr
unfoldNameR nm = callNameT nm >> unfoldR

unfoldAnyR :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => [TH.Name] -> Rewrite c HermitM CoreExpr
unfoldAnyR = orR . map unfoldNameR

unfoldSaturatedR :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
unfoldSaturatedR = callSaturatedT >> unfoldR

specializeR :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
specializeR = unfoldPredR (const $ all isTyCoArg)

-- NOTE: Using a Rewrite because of the way the Kernel is set up.
--       This is a temporary hack until we work out the best way to structure the Kernel.

-- | Stash a binding with a name for later use.
-- Allows us to look at past definitions.
rememberR :: Label -> Rewrite c HermitM Core
rememberR label = sideEffectR $ \ _ -> \case
                                          DefCore def           -> saveDef label def
                                          BindCore (NonRec i e) -> saveDef label (Def i e)
                                          _                     -> fail "remember: not a binding"

-- | Stash a binding with a name for later use.
-- Allows us to look at past definitions.
-- rememberR :: String -> Translate c m Core ()
-- rememberR label = contextfreeT $ \ core ->
--     case core of
--         DefCore def -> saveDef label def
--         BindCore (NonRec i e) -> saveDef label (Def i e)
--         _           -> fail "remember: not a binding"

-- | Apply a stashed definition (like inline, but looks in stash instead of context).
unfoldStashR :: ReadBindings c => String -> Rewrite c HermitM CoreExpr
unfoldStashR label = setFailMsg "Inlining stashed definition failed: " $
                     withPatFailMsg (wrongExprForm "Var v") $
    do (c, Var v) <- exposeT
       constT $ do Def i rhs <- lookupDef label
                   if idName i == idName v -- TODO: Is there a reason we're not just using equality on Id?
                   then ifM ((all (inScope c) . toList) <$> apply freeVarsT c rhs)
                            (return rhs)
                            (fail "some free variables in stashed definition are no longer in scope.")
                   else fail $ "stashed definition applies to " ++ var2String i ++ " not " ++ var2String v

showStashT :: Injection CoreDef a => PrettyC -> PrettyH a -> Translate c HermitM a DocH
showStashT pctx pp = do
    stash <- constT getStash
    docs <- forM (Map.toList stash) $ \ (l,d) -> do
                dfn <- constT $ apply (extractT pp) pctx d
                return $ PP.text ("[ " ++ l ++ " ]") PP.$+$ dfn PP.$+$ PP.space
    return $ PP.vcat docs
