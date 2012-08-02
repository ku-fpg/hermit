module Language.HERMIT.Primitive.Inline where

import GhcPlugins

import Control.Arrow

import Language.HERMIT.GHC
import Language.HERMIT.Primitive.Common
import Language.HERMIT.Primitive.Navigation
-- import Language.HERMIT.Primitive.Debug (traceR)
import Language.HERMIT.Primitive.GHC
import Language.HERMIT.Primitive.Unfold
import Language.HERMIT.Kure
import Language.HERMIT.Context
import Language.HERMIT.External

import qualified Language.Haskell.TH as TH

externals :: [External]
externals =
            [ external "inline" (promoteExprR inline :: RewriteH Core)
                [ "(Var n) ==> <defn of n>, fails otherwise" ].+ Eval .+ Deep .+ TODO
            , external "inline-scrutinee" (promoteExprR inlineScrutinee :: RewriteH Core)
                [ "(Var n) ==> <defn of n>, fails otherwise"
                , "In the case of case binders, replaces with scrutinee expression, "
                , "rather than constructor or literal." ].+ Eval .+ Deep .+ TODO
            , external "inline" (promoteExprR . inlineName :: TH.Name -> RewriteH Core)
                [ "Restrict inlining to a given name" ].+ Eval .+ Deep .+ TODO
            , external "inline-case-binder" (promoteExprR inlineCaseBinder :: RewriteH Core)
                [ "Inline if this variable is a case binder." ].+ Eval .+ Deep .+ Bash .+ TODO
            ]

inlineName :: TH.Name -> RewriteH CoreExpr
inlineName nm = var nm >> inline

inline :: RewriteH CoreExpr
inline = configurableInline False False

inlineScrutinee :: RewriteH CoreExpr
inlineScrutinee = configurableInline True False

inlineCaseBinder :: RewriteH CoreExpr
inlineCaseBinder = configurableInline False True

-- | The implementation of inline, an important transformation.
-- This *only* works on a Var of the given name. It can trivially
-- be prompted to more general cases.
-- TODO: check the scoping for the inline operation; we can mess things up here.
-- Has this TODO been dealt with already?
configurableInline :: Bool -- ^ Inline the scrutinee instead of the patten match (for case binders).
                   -> Bool -- ^ Only inline if this variable is a case binder.
                   -> RewriteH CoreExpr
configurableInline scrutinee caseBinderOnly =
   prefixFailMsg "Inline failed: " $
   withPatFailMsg (wrongExprForm "Var v") $
   do (c, Var v) <- exposeT
      (e,d) <- getUnfolding scrutinee caseBinderOnly v c
      return e >>> accepterR (extractT $ ensureDepth d) "values in inlined expression have been rebound."


-- | Ensure all the free variables in an expression were bound above a given depth.
-- Assumes minimum depth is 0.
ensureDepth :: Int -> TranslateH Core Bool
ensureDepth d = do
    frees <- promoteT freeVarsT
    ds <- collectT $ do c <- contextT
                        promoteExprT $ varT $ \ i -> if i `elem` frees
                                                       then maybe (i,0) (\b -> (i,hermitBindingDepth b)) (lookupHermitBinding i c)
                                                       else (i,0)
    -- traceR $ "greater values (" ++ show d ++ "): " ++ show (filter ((> d) . snd) ds)
    return $ all (toSnd (<= d)) ds

-- | Get list of possible inline targets. Used by shell for completion.
inlineTargets :: TranslateH Core [String]
inlineTargets = collectT $ promoteT $ condM (testM inline)
                                            (varT unqualifiedIdName)
                                            (fail "cannot be inlined.")
