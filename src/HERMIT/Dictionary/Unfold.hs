{-# LANGUAGE FlexibleContexts, ScopedTypeVariables, TupleSections, LambdaCase #-}
module HERMIT.Dictionary.Unfold
    ( externals
    , cleanupUnfoldR
    , rememberR
    , showStashT
    , unfoldR
    , unfoldPredR
    , unfoldNameR
    , unfoldNamesR
    , unfoldSaturatedR
    , unfoldStashR
    , specializeR
    ) where

import Control.Arrow
import Control.Monad

import Data.List (intercalate)
import qualified Data.Map as Map

import HERMIT.PrettyPrinter.Common (DocH, PrettyH, TransformDocH(..), PrettyC)

import HERMIT.Dictionary.Common
import HERMIT.Dictionary.Inline (inlineR)
import HERMIT.Dictionary.Local.Let (letNonRecSubstR)

import HERMIT.Core
import HERMIT.Context
import HERMIT.Kure
import HERMIT.Monad
import HERMIT.External
import HERMIT.GHC

import Prelude hiding (exp)

import qualified Text.PrettyPrint.MarkedHughesPJ as PP

------------------------------------------------------------------------

externals :: [External]
externals =
    [ external "cleanup-unfold" (promoteExprR cleanupUnfoldR :: RewriteH Core)
        [ "Clean up immediately nested fully-applied lambdas, from the bottom up" ] .+ Deep
    , external "remember" (rememberR :: Label -> RewriteH Core)
        [ "Remember the current binding, allowing it to be folded/unfolded in the future." ] .+ Context
    , external "unfold-remembered" (promoteExprR . unfoldStashR :: String -> RewriteH Core)
        [ "Unfold a remembered definition." ] .+ Deep .+ Context
    , external "unfold" (promoteExprR unfoldR :: RewriteH Core)
        [ "In application f x y z, unfold f." ] .+ Deep .+ Context
    , external "unfold" (promoteExprR . unfoldNameR :: String -> RewriteH Core)
        [ "Inline a definition, and apply the arguments; traditional unfold." ] .+ Deep .+ Context
    , external "unfold" (promoteExprR . unfoldNamesR :: [String] -> RewriteH Core)
        [ "Unfold a definition if it is named in the list." ] .+ Deep .+ Context
    , external "unfold-saturated" (promoteExprR unfoldSaturatedR :: RewriteH Core)
        [ "Unfold a definition only if the function is fully applied." ] .+ Deep .+ Context
    , external "specialize" (promoteExprR specializeR :: RewriteH Core)
        [ "Specialize an application to its type and coercion arguments." ] .+ Deep .+ Context
    , external "show-remembered" (TransformDocH showStashT :: TransformDocH CoreTC)
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
    body'' <- andR (replicate (length bnds) letNonRecSubstR) <<< return (mkCoreLets bnds body')
    return $ case comp of
                GT -> mkCoreApps body'' $ drop lenvs args
                _  -> body''

-- | A more powerful 'inline'. Matches two cases:
--      Var ==> inlines
--      App ==> inlines the head of the function call for the app tree
unfoldR :: forall c m. ( AddBindings c, ExtendPath c Crumb, HasEmptyContext c
                       , ReadBindings c, ReadPath c Crumb, MonadCatch m )
        => Rewrite c m CoreExpr
unfoldR = prefixFailMsg "unfold failed: " (go >>> cleanupUnfoldR)
    where go :: Rewrite c m CoreExpr
          go = appAllR go idR <+ inlineR -- this order gives better error messages

unfoldPredR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, ReadBindings c, HasEmptyContext c) => (Id -> [CoreExpr] -> Bool) -> Rewrite c HermitM CoreExpr
unfoldPredR p = callPredT p >> unfoldR

unfoldNameR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, ReadBindings c, HasEmptyContext c) => String -> Rewrite c HermitM CoreExpr
unfoldNameR nm = prefixFailMsg ("unfold '" ++ nm ++ " failed: ") (callNameT nm >> unfoldR)

unfoldNamesR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, ReadBindings c, HasEmptyContext c) => [String] -> Rewrite c HermitM CoreExpr
unfoldNamesR []  = fail "unfold-names failed: no names given."
unfoldNamesR nms = setFailMsg "unfold-names failed." $
                   orR (map unfoldNameR nms)

unfoldSaturatedR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, ReadBindings c, HasEmptyContext c) => Rewrite c HermitM CoreExpr
unfoldSaturatedR = callSaturatedT >> unfoldR

specializeR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, ReadBindings c, HasEmptyContext c) => Rewrite c HermitM CoreExpr
specializeR = unfoldPredR (const $ all isTyCoArg)

-- NOTE: Using a Rewrite because of the way the Kernel is set up.
--       This is a temporary hack until we work out the best way to structure the Kernel.

-- | Stash a binding with a name for later use.
-- Allows us to look at past definitions.
rememberR :: Label -> Rewrite c HermitM Core
rememberR label = sideEffectR $ \ _ -> \case
                                          DefCore def           -> saveDef label def
                                          BindCore (NonRec i e) -> saveDef label (Def i e)
                                          _                     -> fail "remember failed: not applied to a binding."

-- | Stash a binding with a name for later use.
-- Allows us to look at past definitions.
-- rememberR :: String -> Transform c m Core ()
-- rememberR label = contextfreeT $ \ core ->
--     case core of
--         DefCore def -> saveDef label def
--         BindCore (NonRec i e) -> saveDef label (Def i e)
--         _           -> fail "remember: not a binding"

-- | Apply a stashed definition (like inline, but looks in stash instead of context).
unfoldStashR :: ReadBindings c => String -> Rewrite c HermitM CoreExpr
unfoldStashR label = prefixFailMsg "Inlining stashed definition failed: " $
                     withPatFailMsg (wrongExprForm "Var v") $
    do (c, Var v) <- exposeT
       constT $ do Def i rhs <- lookupDef label
                   dflags <- getDynFlags
                   if idName i == idName v -- TODO: Is there a reason we're not just using equality on Id?
                   then let fvars = varSetElems $ localFreeVarsExpr rhs
                        in if all (inScope c) fvars
                           then return rhs
                           else fail $ "free variables " ++ intercalate "," (map (showPpr dflags) (filter (not . inScope c) fvars)) ++ " in stashed definition are no longer in scope."
                   else fail $ "stashed definition applies to " ++ var2String i ++ " not " ++ var2String v

showStashT :: Injection CoreDef a => PrettyC -> PrettyH a -> Transform c HermitM a DocH
showStashT pctx pp = do
    stash <- constT getStash
    docs <- forM (Map.toList stash) $ \ (l,d) -> do
                dfn <- constT $ apply (extractT pp) pctx d
                return $ PP.text ("[ " ++ l ++ " ]") PP.$+$ dfn PP.$+$ PP.space
    return $ PP.vcat docs
