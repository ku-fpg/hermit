module LoadR
  (  -- * Converting Scripts to Rewrites
     exprHToRewrite
  )
where

import Control.Arrow
import Control.Applicative

import Language.HERMIT.Context(LocalPathH)
import Language.HERMIT.Kure
import Language.HERMIT.Parser
import Language.HERMIT.External
import Language.HERMIT.Interp

------------------------------------

data LoadR = LoadScope [LoadR]
           | LoadRewriteHCore (RewriteH Core)
--           | LoadRewriteHCoreTC (RewriteH CoreTC)
--           | LoadBiRewriteHCore (BiRewriteH Core)
           | LoadPath PathH
           | LoadTranslateHCorePath (TranslateH Core LocalPathH)

-----------------------------------

interpLoadR :: [Interp LoadR]
interpLoadR =
                [ interp (\ (RewriteCoreBox r)        -> LoadRewriteHCore r)
--                , interp (\ (RewriteCoreTCBox r)      -> LoadRewriteHCoreTC r)  -- just consider Core for now, for simplicity
--                , interp (\ (BiRewriteCoreBox br)     -> LoadBiRewriteHCore br) -- the script writer should specify the direction
                , interp (\ (CrumbBox cr)             -> LoadPath [cr])
                , interp (\ (PathBox p)               -> LoadPath (snocPathToPath p))
                , interp (\ (TranslateCorePathBox t)  -> LoadTranslateHCorePath t)
                ]

------------------------------------

loadExprH :: Dictionary -> ExprH -> KureM LoadR
loadExprH dict (ListH es)  = LoadScope <$> mapM (loadExprH dict) es
loadExprH dict e           = interpExprH dict interpLoadR e

-----------------------------------

loadsToRewrite :: [LoadR] -> RewriteH Core
loadsToRewrite []        = idR
loadsToRewrite (l : ls)  = let rest = loadsToRewrite ls
                            in case l of
                                 LoadScope ls1            -> loadsToRewrite ls1 >>> rest
                                 LoadRewriteHCore r       -> r >>> rest
                                 LoadPath p               -> pathR p rest
                                 LoadTranslateHCorePath t -> do p <- t
                                                                localPathR p rest

loadToRewrite :: LoadR -> RewriteH Core
loadToRewrite l = loadsToRewrite [l]

-----------------------------------

-- | Interpret an ExprH as a Rewrite in the presences of a specific Dictionary.
--   Will fail for expressions that cannot be converted into rewrites.
exprHToRewrite :: Dictionary -> ExprH -> KureM (RewriteH Core)
exprHToRewrite dict e = loadToRewrite <$> loadExprH dict e

-----------------------------------
