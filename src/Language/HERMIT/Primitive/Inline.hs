module Language.HERMIT.Primitive.Inline where

import GhcPlugins

import Control.Arrow

import Language.HERMIT.Primitive.Consider
import Language.HERMIT.Kure
import Language.HERMIT.Context
import Language.HERMIT.External

import qualified Language.Haskell.TH as TH

externals :: [External]
externals = map (.+ Context)
            [ external "inline" (promoteR inline :: RewriteH Core)
                [ "(Var n) ==> <defn of n>, fails otherwise" ]
            , external "inline" (promoteR . inlineName :: TH.Name -> RewriteH Core)
                [ "Restrict inlining to a given name" ]
            ]

inlineName :: TH.Name -> RewriteH CoreExpr
inlineName nm = var nm >>> inline

-- | The implementation of inline, an important transformation.
-- This *only* works on a Var of the given name. It can trivially
-- be prompted to more general cases.
inline :: RewriteH CoreExpr
inline = rewrite $ \ c e -> case e of
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
    _      -> fail "inline failed (No variable)"
