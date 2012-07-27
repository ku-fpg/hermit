module Language.HERMIT.Primitive.Inline where

import GhcPlugins

import Language.HERMIT.GHC
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
            [ external "inline" (promoteExprR (inline False) :: RewriteH Core)
                [ "(Var n) ==> <defn of n>, fails otherwise" ].+ Eval .+ Deep .+ TODO
            , external "inline-scrutinee" (promoteExprR (inline True) :: RewriteH Core)
                [ "(Var n) ==> <defn of n>, fails otherwise"
                , "In the case of case wildcard binders, replaces with scrutinee expression, "
                , "rather than constructor or literal." ].+ Eval .+ Deep .+ TODO
            , external "inline" (promoteExprR . inlineName :: TH.Name -> RewriteH Core)
                [ "Restrict inlining to a given name" ].+ Eval .+ Deep .+ TODO
            -- , external "inline-case-constructor" (promoteExprR inlineCaseConstructor :: RewriteH Core)
            --     [ "Inline the wildcard binder of the current case expression." ].+ Eval .+ Deep .+ TODO -- .+ Bash
            ]

inlineName :: TH.Name -> RewriteH CoreExpr
inlineName nm = var nm >> inline False

-- | The implementation of inline, an important transformation.
-- This *only* works on a Var of the given name. It can trivially
-- be prompted to more general cases.
-- TODO: check the scoping for the inline operation; we can mess things up here.
inline :: Bool -> RewriteH CoreExpr
inline scrutinee = prefixFailMsg "Inline failed: " $
  rewrite $ \ c e -> case e of
    Var v  -> -- A candiate for inlining
              either fail (\(e',d) -> condM (apply (extractT (ensureDepth d)) c e')
                                            (return e')
                                            (fail "values in inlined expression have been rebound."))
                     (getUnfolding scrutinee v c)
    _      -> fail "not a variable."

-- Doesn't work.  We don't want to inline things that share the same TH.Name.
-- inlineCaseConstructor :: RewriteH CoreExpr
-- inlineCaseConstructor = do Case _ v _ _ <- idR
--                            extractR $ anybuR $ promoteExprR $ inlineName $ id2THName v

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
                                            (varT unqualifiedIdName)
                                            (fail "cannot be inlined")
