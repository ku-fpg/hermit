{-# LANGUAGE FlexibleContexts, ScopedTypeVariables, TupleSections, LambdaCase #-}
module HERMIT.Dictionary.Unfold
    ( externals
    , betaReducePlusR
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
import Control.Monad.IO.Class

import Data.List (intercalate)
import qualified Data.Map as Map

import HERMIT.PrettyPrinter.Common (DocH, PrettyH, TransformDocH(..), PrettyC)

import HERMIT.Dictionary.Common
import HERMIT.Dictionary.GHC (substCoreExpr)
import HERMIT.Dictionary.Inline (inlineR)

import HERMIT.Core
import HERMIT.Context
import HERMIT.External
import HERMIT.GHC
import HERMIT.Kure
import HERMIT.Monad
import HERMIT.Name

import Prelude hiding (exp)

import qualified Text.PrettyPrint.MarkedHughesPJ as PP

------------------------------------------------------------------------

externals :: [External]
externals =
    [ external "beta-reduce-plus" (promoteExprR betaReducePlusR :: RewriteH Core)
        [ "Perform one or more beta-reductions."]                               .+ Eval .+ Shallow
    , external "remember" (rememberR :: RememberedName -> RewriteH Core)
        [ "Remember the current binding, allowing it to be folded/unfolded in the future." ] .+ Context
    , external "unfold-remembered" (promoteExprR . unfoldStashR :: RememberedName -> RewriteH Core)
        [ "Unfold a remembered definition." ] .+ Deep .+ Context
    , external "unfold" (promoteExprR unfoldR :: RewriteH Core)
        [ "In application f x y z, unfold f." ] .+ Deep .+ Context
    , external "unfold" (promoteExprR . unfoldNameR . unOccurrenceName :: OccurrenceName -> RewriteH Core)
        [ "Inline a definition, and apply the arguments; traditional unfold." ] .+ Deep .+ Context
    , external "unfold" (promoteExprR . unfoldNamesR . map unOccurrenceName:: [OccurrenceName] -> RewriteH Core)
        [ "Unfold a definition if it is named in the list." ] .+ Deep .+ Context
    , external "unfold-saturated" (promoteExprR unfoldSaturatedR :: RewriteH Core)
        [ "Unfold a definition only if the function is fully applied." ] .+ Deep .+ Context
    , external "specialize" (promoteExprR specializeR :: RewriteH Core)
        [ "Specialize an application to its type and coercion arguments." ] .+ Deep .+ Context
    , external "show-remembered" (TransformDocH showStashT :: TransformDocH CoreTC)
        [ "Display all remembered definitions." ]
    ]

------------------------------------------------------------------------

-- | Perform one or more beta reductions.
betaReducePlusR :: MonadCatch m => Rewrite c m CoreExpr
betaReducePlusR = prefixFailMsg "Multi-beta-reduction failed: " $ do
    (f,args) <- callT
    let (f',args',atLeastOne) = reduceAll f args False
        reduceAll (Lam v body) (a:as) _ = reduceAll (substCoreExpr v a body) as True
        reduceAll e            as     b = (e,as,b)
    guardMsg atLeastOne "no beta reductions possible."
    return $ mkCoreApps f' args'

-- | A more powerful 'inline'. Matches two cases:
--      Var ==> inlines
--      App ==> inlines the head of the function call for the app tree
unfoldR :: forall c m. ( AddBindings c, ExtendPath c Crumb, HasEmptyContext c
                       , ReadBindings c, ReadPath c Crumb, MonadCatch m, MonadUnique m )
        => Rewrite c m CoreExpr
unfoldR = prefixFailMsg "unfold failed: " (go >>> tryR betaReducePlusR)
    where go :: Rewrite c m CoreExpr
          go = appAllR go idR <+ inlineR -- this order gives better error messages

unfoldPredR :: ( AddBindings c, ExtendPath c Crumb, HasEmptyContext c, ReadBindings c, ReadPath c Crumb
               , MonadCatch m, MonadUnique m )
            => (Id -> [CoreExpr] -> Bool) -> Rewrite c m CoreExpr
unfoldPredR p = callPredT p >> unfoldR

unfoldNameR :: ( ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, ReadBindings c, HasEmptyContext c
               , HasHermitMEnv m, HasHscEnv m, MonadCatch m, MonadIO m, MonadThings m, MonadUnique m )
            => String -> Rewrite c m CoreExpr
unfoldNameR nm = prefixFailMsg ("unfold '" ++ nm ++ " failed: ") (callNameT nm >> unfoldR)

unfoldNamesR :: ( ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, ReadBindings c, HasEmptyContext c
                , HasHermitMEnv m, HasHscEnv m, MonadCatch m, MonadIO m, MonadThings m, MonadUnique m )
             => [String] -> Rewrite c m CoreExpr
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
rememberR :: RememberedName -> Rewrite c HermitM Core
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
unfoldStashR :: ReadBindings c => RememberedName -> Rewrite c HermitM CoreExpr
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
                   else fail $ "stashed definition applies to " ++ unqualifiedName i ++ " not " ++ unqualifiedName v

showStashT :: Injection CoreDef a => PrettyC -> PrettyH a -> Transform c HermitM a DocH
showStashT pctx pp = do
    stash <- constT getStash
    docs <- forM (Map.toList stash) $ \ (l,d) -> do
                dfn <- constT $ applyT (extractT pp) pctx d
                return $ PP.text ("[ " ++ show l ++ " ]") PP.$+$ dfn PP.$+$ PP.space
    return $ PP.vcat docs
