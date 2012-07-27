{-# LANGUAGE ScopedTypeVariables, TypeFamilies, FlexibleContexts, TupleSections #-}
module Language.HERMIT.Primitive.Unfold where

import GhcPlugins hiding (empty)
import Control.Monad

import Language.HERMIT.Primitive.GHC

import Language.HERMIT.CoreExtra
import Language.HERMIT.Kure
import Language.HERMIT.Monad
import Language.HERMIT.External
import Language.HERMIT.Context

import Prelude hiding (exp)

------------------------------------------------------------------------

externals :: [External]
externals =
         [ external "stash-defn" stashDef
                ["stash-defn"]
         , external "stash-apply" (promoteExprR . stashApply)
                ["stash-apply"]
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

-- | Apply a stashed definition (like inline, but looks in stash instead of context)
stashApply :: String -> RewriteH CoreExpr
stashApply label = translate $ \ c e -> do
    Def i rhs <- lookupDef label
    case e of
        Var i' -> if idName i == idName i'
                    then do rhsFrees <- apply freeVarsT c rhs
                            if all (inScope c) rhsFrees
                              then return rhs
                              else fail "stashApply: some frees in stashed definition are no longer in scope"
                    else fail $ "stashApply: stashed definition applies to: " ++ showPpr i ++ " not: " ++ showPpr i'
        _ -> fail "stashApply: not a Var"

-- | See whether an Id is in scope.
inScope :: Context -> Id -> Bool
inScope c i = maybe (case unfoldingInfo (idInfo i) of
                        CoreUnfolding {} -> True -- defined elsewhere
                        _ -> False)
                    (const True) -- defined in this module
                    (lookupHermitBinding i c)

getUnfolding :: Monad m
             => Bool -- ^ If True, then for case binders inline the scrutinee.
             -> Id -> Context -> m (CoreExpr, Int)
getUnfolding scrutinee i c =
    case lookupHermitBinding i c of
        Nothing -> case unfoldingInfo (idInfo i) of
                     CoreUnfolding { uf_tmpl = uft } -> return (uft, 0)
                     _ -> fail $ "cannot find " ++ show i ++ " in Env or IdInfo"
        Just (LAM {}) -> fail $ show i ++ " is lambda-bound"
        Just (BIND depth _ e') -> return (e', depth)
        Just (CASE depth s coreAlt) ->
            if scrutinee then return (s, depth)
            else let tys = tyConAppArgs (idType i)
                 in return $ either (,depth) (,depth+1) (alt2Exp s tys coreAlt)

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
