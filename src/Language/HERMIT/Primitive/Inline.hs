module Language.HERMIT.Primitive.Inline
         ( -- * Inlining
           externals
         , inline
         , inlineName
         , inlineScrutinee
         , inlineCaseBinder
         , inlineTargets
         )

where

import GhcPlugins

import Control.Arrow

import Language.HERMIT.Core
import Language.HERMIT.Kure
import Language.HERMIT.Context
import Language.HERMIT.GHC
import Language.HERMIT.External

import Language.HERMIT.Primitive.Common
-- import Language.HERMIT.Primitive.Debug (traceR)
import Language.HERMIT.Primitive.GHC hiding (externals)
import Language.HERMIT.Primitive.Unfold hiding (externals)

import qualified Language.Haskell.TH as TH

------------------------------------------------------------------------

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

------------------------------------------------------------------------

-- | If the current variable matches the given name, then inline it.
inlineName :: TH.Name -> RewriteH CoreExpr
inlineName nm = let name = TH.nameBase nm in
                prefixFailMsg ("inline '" ++ name ++ " failed: ") $
                withPatFailMsg (wrongExprForm "Var v") $
   do Var v <- idR
      guardMsg (cmpTHName2Id nm v) $ name ++ " does not match " ++ var2String v ++ "."
      inline

-- | Inline the current variable.
inline :: RewriteH CoreExpr
inline = configurableInline False False

-- | Inline the current variable, using the scrutinee rather than the case alternative if it is a case wild-card binder.
inlineScrutinee :: RewriteH CoreExpr
inlineScrutinee = configurableInline True False

-- | If the current variable is a case wild-card binder, then inline it.
inlineCaseBinder :: RewriteH CoreExpr
inlineCaseBinder = configurableInline False True

-- | The implementation of inline, an important transformation.
-- This *only* works on a Var of the given name. It can trivially
-- be prompted to more general cases.
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
inlineTargets = collectT $ promoteT $ whenM (testM inline) (varT unqualifiedIdName)

------------------------------------------------------------------------
