{-# LANGUAGE ScopedTypeVariables, TypeFamilies, FlexibleContexts, TupleSections #-}
module Language.HERMIT.Primitive.Unfold
    ( externals
    , stashDef
    , stashApply
    , getUnfolding
    ) where

import GhcPlugins hiding (empty)
import Control.Monad
import Control.Applicative

import Language.HERMIT.Primitive.GHC hiding (externals)
import Language.HERMIT.Primitive.Common

import Language.HERMIT.CoreExtra
import Language.HERMIT.Kure
import Language.HERMIT.Monad
import Language.HERMIT.External
import Language.HERMIT.Context

import Prelude hiding (exp)

------------------------------------------------------------------------

externals :: [External]
externals =
         [ external "remember" stashDef
                ["Remember the current binding, allowing it to be folded/unfolded in the future."]
         , external "unfold" (promoteExprR . stashApply)
                ["Unfold a remembered definition."]
         ]

------------------------------------------------------------------------

-- NOTE: Using a Rewrite because of the way the Kernel is set up.
--       This is a temperary hack until we work out the best way to structure the Kernel.

-- | Stash a binding with a name for later use.
-- Allows us to look at past definitions.
stashDef :: String -> RewriteH Core
stashDef label = sideEffectR $ \ _ core ->
  case core of
    DefCore def           -> saveDef label def
    BindCore (NonRec i e) -> saveDef label (Def i e)
    _                     -> fail "stashDef: not a binding"

-- | Stash a binding with a name for later use.
-- Allows us to look at past definitions.
-- stashDef :: String -> TranslateH Core ()
-- stashDef label = contextfreeT $ \ core ->
--     case core of
--         DefCore def -> saveDef label def
--         BindCore (NonRec i e) -> saveDef label (Def i e)
--         _           -> fail "stashDef: not a binding"

-- | Apply a stashed definition (like inline, but looks in stash instead of context).
stashApply :: String -> RewriteH CoreExpr
stashApply label = setFailMsg "Inlining stashed definition failed: " $
                   withPatFailMsg (wrongExprForm "Var v") $
                   do (c, Var v) <- exposeT
                      constT $ do Def i rhs <- lookupDef label
                                  if idName i == idName v -- Is there a reason we're not just using equality on Id?
                                    then ifM (all (inScope c) <$> apply freeVarsT c rhs)
                                             (return rhs)
                                             (fail "some free variables in stashed definition are no longer in scope.")
                                    else fail $ "stashed definition applies to " ++ showPpr i ++ " not " ++ showPpr v

getUnfolding :: Monad m
             => Bool -- ^ Get the scrutinee instead of the patten match (for case binders).
             -> Bool -- ^ Only succeed if this variable is a case binder.
             -> Id -> Context -> m (CoreExpr, Int)
getUnfolding scrutinee caseBinderOnly i c =
    case lookupHermitBinding i c of
        Nothing -> case unfoldingInfo (idInfo i) of
                     CoreUnfolding { uf_tmpl = uft } -> if caseBinderOnly then fail "not a case binder" else return (uft, 0)
                     _                               -> fail $ "cannot find " ++ show i ++ " in Env or IdInfo."
        Just (LAM {}) -> fail $ show i ++ " is lambda-bound"
        Just (BIND depth _ e') -> if caseBinderOnly then fail "not a case binder" else return (e', depth)
        Just (CASE depth s coreAlt) -> return $ if scrutinee
                                                 then (s, depth)
                                                 else let tys = tyConAppArgs (idType i)
                                                       in either (,depth) (,depth+1) (alt2Exp s tys coreAlt)

-- | Convert lhs of case alternative to a constructor application expression,
--   or a default expression in the case of the DEFAULT alternative.
--   Accepts a list of types to apply to the constructor before the value args.
--
-- > data T a b = C a b Int
--
-- Pseudocode:
--
-- > alt2Exp (...) [a,b] (C, [x,y,z]) ==> C a b (x::a) (y::b) (z::Int)
--
-- The 'Either' denotes whether we picked the default (scrutinee) or built an expression.
-- This matters for the depth check.
alt2Exp :: CoreExpr -> [Type] -> (AltCon,[Id]) -> Either CoreExpr CoreExpr
alt2Exp d _   (DEFAULT   , _ ) = Left d
alt2Exp _ _   (LitAlt l  , _ ) = Right $ Lit l
alt2Exp _ tys (DataAlt dc, as) = Right $ mkCoreConApps dc (map Type tys ++ map Var as)
