{-# LANGUAGE TupleSections #-}
module Language.HERMIT.Primitive.Inline where

import GhcPlugins

import Control.Arrow

import Language.HERMIT.Primitive.Consider
-- import Language.HERMIT.Primitive.Debug (traceR)
import Language.HERMIT.Primitive.GHC
import Language.HERMIT.Kure
import Language.HERMIT.Context
import Language.HERMIT.External

import qualified Language.Haskell.TH as TH

externals :: [External]
externals =
            [ external "inline" (promoteExprR (inline False) :: RewriteH Core)
                [ "(Var n) ==> <defn of n>, fails otherwise" ].+ Eval .+ Deep .+ TODO
            , external "inline-scrutinee" (promoteExprR (inline True) :: RewriteH Core)
                [ "(Var n) ==> <defn of n>, fails otherwise"
                , "In the case of case wildcard binders, replaces with scrutinee expression, "
                , "rather than constructor or literal." ].+ Eval .+ Deep .+ TODO
            , external "inline" (promoteExprR . inlineName :: TH.Name -> RewriteH Core)
                [ "Restrict inlining to a given name" ].+ Eval .+ Deep .+ TODO
            ]

inlineName :: TH.Name -> RewriteH CoreExpr
inlineName nm = var nm >>> inline False

-- | The implementation of inline, an important transformation.
-- This *only* works on a Var of the given name. It can trivially
-- be prompted to more general cases.
-- TODO: check the scoping for the inline operation; we can mess things up here.
inline :: Bool -> RewriteH CoreExpr
inline scrutinee = rewrite $ \ c e -> case e of
    Var n0 -> -- A candiate for inlining
              case lookupHermitBinding n0 c of
                Nothing       -> do
                  let info = idInfo n0
                  case unfoldingInfo info of
                    -- This was simple, once we knew where to look
                    CoreUnfolding { uf_tmpl = uft } -> return uft
                    _ -> fail $ "inline failed, cannot find " ++ show n0 ++ "  in Env or IdInfo"
                Just (LAM {}) -> fail $ "inline failed, found lambda-bound value or type"
                Just (BIND depth _ e') ->
                    condM (apply (extractT (ensureDepth depth)) c e')
                          (return e')
                          (fail "values in inlined expression have been rebound")
                Just (CASE depth s coreAlt) ->
                    if scrutinee then return s
                    else let tys = tyConAppArgs (idType n0)
                             (e',d') = either (,depth) (,depth+1) (alt2Exp s tys coreAlt)
                         in condM (apply (extractT (ensureDepth d')) c e')
                                  (return e')
                                  (fail "values in inlined expression have been rebound")

    _      -> fail "inline failed (No variable)"

-- | Convert lhs of case alternative to a constructor application expression,
-- or a default expression in the case of the DEFAULT alternative.
-- Accepts a list of types to apply to the constructor before the value args.
--
-- > data T a b = C a b Int
-- Pseudocode:
-- > alt2Exp (...) [a,b] (C, [x,y,z]) ==> C a b (x::a) (y::b) (z::Int)
--
-- The Either denotes whether we picked the default (scrutinee) or built an expression.
-- This matters for the depth check.
alt2Exp :: CoreExpr -> [Type] -> (AltCon,[Id]) -> Either CoreExpr CoreExpr
alt2Exp d _   (DEFAULT   , _ ) = Left d
alt2Exp _ _   (LitAlt l  , _ ) = Right $ Lit l
alt2Exp _ tys (DataAlt dc, as) = Right $ mkCoreConApps dc (map Type tys ++ map Var as)

-- | Ensure all the free variables in an expression were bound above a given depth.
-- Assumes minimum depth is 0.
ensureDepth :: Int -> TranslateH Core Bool
ensureDepth d = do
    frees <- promoteT freeVarsT
    ds <- collectT (do c <- contextT
                       promoteT $ varT $ \ i -> if i `elem` frees
                                                then maybe (i,0) (\b -> (i,hermitBindingDepth b)) (lookupHermitBinding i c)
                                                else (i,0))
    -- traceR $ "greater values (" ++ show d ++ "): " ++ show (filter ((> d) . snd) ds)
    return $ all (<= d) $ map snd ds

-- | Get list of possible inline targets. Used by shell for completion.
inlineTargets :: TranslateH Core [String]
inlineTargets = collectT $ promoteT $ condM (testM (inline False))
                                            (varT unqualified)
                                            (fail "cannot be inlined")
