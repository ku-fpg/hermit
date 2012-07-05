module Language.HERMIT.Primitive.Inline where

import GhcPlugins

import Control.Arrow

import Language.HERMIT.Primitive.Consider
import Language.HERMIT.Kure
import Language.HERMIT.Context
import Language.HERMIT.External

import qualified Language.Haskell.TH as TH

externals :: [External]
externals =
            [ external "inline" (promoteR (inline False) :: RewriteH Core)
                [ "(Var n) ==> <defn of n>, fails otherwise" ].+ Eval .+ Deep .+ TODO
            , external "inline-scrutinee" (promoteR (inline True) :: RewriteH Core)
                [ "(Var n) ==> <defn of n>, fails otherwise"
                , "In the case of case wildcard binders, replaces with scrutinee expression, "
                , "rather than constructor or literal." ].+ Eval .+ Deep .+ TODO
            , external "inline" (promoteR . inlineName :: TH.Name -> RewriteH Core)
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
                Just (BIND _depth _ e')
                  -- need to check for clashes, based on the depth
                  -- for now, just accept, and proceeded
                  -> return e'
                Just (CASE _d s conApp) -> return $ if scrutinee then s else conApp
    _      -> fail "inline failed (No variable)"

-- | Get list of possible inline targets. Used by shell for completion.
inlineTargets :: TranslateH Core [String]
inlineTargets = collectT $ promoteT $ condM (testM (inline False))
                                            (varT unqualified)
                                            (fail "cannot be inlined")
