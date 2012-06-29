module Language.HERMIT.Primitive.Kure where

import Control.Arrow

import Language.HERMIT.Kure
import Language.HERMIT.External

------------------------------------------------------------------------------------

-- external "<+" ((<+) :: TranslateH a b -> TranslateH a b -> TranslateH a b)
     --   (>->) :: Monad m => Translate c m a b -> Translate c m b d -> Translate c m a d

externals :: [External]
externals = map (.+ KURE)
   [ external "id"         (idR :: RewriteH Core)
       [ "perform the identity"] .+ Shallow
   , external "<+"         ((<+) :: RewriteH Core -> RewriteH Core -> RewriteH Core)
       [ "perform the first translate, and then, if it fails, perform the second rewrite" ]
   , external ">>>"        ((>>>) :: RewriteH Core -> RewriteH Core -> RewriteH Core)
       [ "compose rewrites, requiring both to succeed" ]
   , external ">+>"        ((>+>) :: RewriteH Core -> RewriteH Core -> RewriteH Core)
       [ "compose rewrites, allowing one to fail" ]
   , external "try"        (tryR :: RewriteH Core -> RewriteH Core)
       [ "tries a rewrite, and performs an identity if this rewrite fails" ]
   , external "repeat"     (repeatR :: RewriteH Core -> RewriteH Core)
       [ "repeats a rewrite until it would fail" ] .+ Cycle
   , external "all"        (allR :: RewriteH Core -> RewriteH Core)
       [ "apply a rewrite to all children of the node, requiring success at every child" ]
   , external "any"        (anyR :: RewriteH Core -> RewriteH Core)
       [ "apply a rewrite to all children of the node, requiring success for at least one child" ]
   , external "all-bu"     (allbuR :: RewriteH Core -> RewriteH Core)
       [ "promotes a rewrite to operate over an entire tree in bottom-up order, requiring success at each node" ] .+ Deep
   , external "all-td"     (alltdR :: RewriteH Core -> RewriteH Core)
       [ "promotes a rewrite to operate over an entire tree in top-down order, requiring success at every node" ] .+ Deep
   , external "any-bu"     (anybuR :: RewriteH Core -> RewriteH Core)
       [ "promotes a rewrite to operate over an entire tree in bottom-up order, requiring success for at least one node" ] .+ Deep
   , external "any-td"     (anytdR :: RewriteH Core -> RewriteH Core)
       [ "promotes a rewrite to operate over an entire tree in top-down order, requiring success for at least one node" ] .+ Deep
   , external "all-du"     (allduR :: RewriteH Core -> RewriteH Core)
       [ "apply a rewrite twice, in a top-down and bottom-up way, using one single tree traversal",
         "succeeding if they all succeed"] .+ Deep
   , external "any-du"     (anyduR :: RewriteH Core -> RewriteH Core)
       [ "apply a rewrite twice, in a top-down and bottom-up way, using one single tree traversal",
         "succeeding if any succeed"] .+ Deep
   , external "prune-td"   (prunetdR :: RewriteH Core -> RewriteH Core)
       [ "attempt to apply a rewrite in a top-down manner, prunning at successful rewrites" ] .+ Deep
   , external "innermost"  (innermostR :: RewriteH Core -> RewriteH Core)
       [ "a fixed-point traveral, starting with the innermost term" ] .+ Deep .+ Cycle
   , external "focus"      (hfocusR :: TranslateH Core Path -> RewriteH Core -> RewriteH Core)
       [ "apply a rewrite to a focal point"] .+ Focus .+ Deep
   , external "focus"      (hfocusT :: TranslateH Core Path -> TranslateH Core String -> TranslateH Core String)
       [ "apply a query at a focal point"] .+ Focus .+ Deep
   ]

hfocusR :: TranslateH Core Path -> RewriteH Core -> RewriteH Core
hfocusR tp r = do p <- tp
                  pathR p r

hfocusT :: TranslateH Core Path -> TranslateH Core String -> TranslateH Core String
hfocusT tp t = do p <- tp
                  pathT p t

------------------------------------------------------------------------------------
