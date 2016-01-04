{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module HERMIT.Dictionary.Unfold
    ( externals
    , betaReducePlusR
    , unfoldR
    , unfoldPredR
    , unfoldNameR
    , unfoldNamesR
    , unfoldSaturatedR
    , specializeR
    ) where

import Control.Arrow
import Control.Monad

import HERMIT.Dictionary.Common
import HERMIT.Dictionary.Inline (inlineR)

import HERMIT.Core
import HERMIT.Context
import HERMIT.External
import HERMIT.GHC
import HERMIT.Kure
import HERMIT.Monad
import HERMIT.Name

import Prelude hiding (exp)

------------------------------------------------------------------------

externals :: [External]
externals =
    [ external "beta-reduce-plus" (promoteExprR betaReducePlusR :: RewriteH LCore)
        [ "Perform one or more beta-reductions."]                               .+ Eval .+ Shallow
    , external "unfold" (promoteExprR unfoldR :: RewriteH LCore)
        [ "In application f x y z, unfold f." ] .+ Deep .+ Context
    , external "unfold" (promoteExprR . unfoldNameR . unOccurrenceName :: OccurrenceName -> RewriteH LCore)
        [ "Inline a definition, and apply the arguments; traditional unfold." ] .+ Deep .+ Context
    , external "unfold" (promoteExprR . unfoldNamesR . map unOccurrenceName:: [OccurrenceName] -> RewriteH LCore)
        [ "Unfold a definition if it is named in the list." ] .+ Deep .+ Context
    , external "unfold-saturated" (promoteExprR unfoldSaturatedR :: RewriteH LCore)
        [ "Unfold a definition only if the function is fully applied." ] .+ Deep .+ Context
    , external "specialize" (promoteExprR specializeR :: RewriteH LCore)
        [ "Specialize an application to its type and coercion arguments." ] .+ Deep .+ Context
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
                       , ReadBindings c, ReadPath c Crumb, MonadCatch m )
        => Rewrite c m CoreExpr
unfoldR = prefixFailMsg "unfold failed: " (go >>> tryR betaReducePlusR)
    where go :: Rewrite c m CoreExpr
          go = appAllR go idR <+ inlineR -- this order gives better error messages

unfoldPredR :: ( AddBindings c, ExtendPath c Crumb, HasEmptyContext c, ReadBindings c, ReadPath c Crumb
               , MonadCatch m )
            => (Id -> [CoreExpr] -> Bool) -> Rewrite c m CoreExpr
unfoldPredR p = callPredT p >> unfoldR

unfoldNameR :: ( ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, ReadBindings c, HasEmptyContext c
               , MonadCatch m )
            => HermitName -> Rewrite c m CoreExpr
unfoldNameR nm = prefixFailMsg ("unfold '" ++ show nm ++ " failed: ") (callNameT nm >> unfoldR)

unfoldNamesR :: ( ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, ReadBindings c, HasEmptyContext c
                , MonadCatch m )
             => [HermitName] -> Rewrite c m CoreExpr
unfoldNamesR []  = fail "unfold-names failed: no names given."
unfoldNamesR nms = setFailMsg "unfold-names failed." $ orR (map unfoldNameR nms)

unfoldSaturatedR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, ReadBindings c, HasEmptyContext c) => Rewrite c HermitM CoreExpr
unfoldSaturatedR = callSaturatedT >> unfoldR

specializeR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, ReadBindings c, HasEmptyContext c) => Rewrite c HermitM CoreExpr
specializeR = unfoldPredR (const $ all isTyCoArg)
