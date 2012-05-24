module Language.HERMIT.Primitive.Kure where

import Language.KURE

import Language.HERMIT.HermitKure
import Language.HERMIT.External

------------------------------------------------------------------------------------

-- external "<+" ((<+) :: TranslateH a b -> TranslateH a b -> TranslateH a b)
     --   (>->) :: Monad m => Translate c m a b -> Translate c m b d -> Translate c m a d

externals :: [External]
externals = map (.+ KURE)
   [ external "id"         (idR :: RewriteH Core)
       [ "perform the identity"]
   , external "catch"      ((<+) :: RewriteH Core -> RewriteH Core -> RewriteH Core)
       [ "perform the first translate, and then, if it fails, perform the second rewrite" ]
   , external "compose"    ((>->) :: RewriteH Core -> RewriteH Core -> RewriteH Core)
       [ "compose rewrites, requiring both to succeed" ]
   , external "both"       ((>+>) :: RewriteH Core -> RewriteH Core -> RewriteH Core)
       [ "compose rewrites, allowing one to fail" ]
   , external "try"        (tryR :: RewriteH Core -> RewriteH Core)
       [ "tries a rewrite, and performs an identity if this rewrite fails" ]
   , external "repeat"     (repeatR :: RewriteH Core -> RewriteH Core)
       [ "repeats a rewrite until it would fail" ]
   , external "all"        (allR :: RewriteH Core -> RewriteH Core)
       [ "apply a rewrite to all children of the node, requiring success at every child" ]
   , external "any"        (anyR :: RewriteH Core -> RewriteH Core)
       [ "apply a rewrite to all children of the node, requiring success for at least one child" ]
   , external "allbu"      (allbuR :: RewriteH Core -> RewriteH Core)
       [ "promotes a rewrite to operate over an entire tree in bottom-up order, requiring success at each node" ]
   , external "alltd"      (alltdR :: RewriteH Core -> RewriteH Core)
       [ "promotes a rewrite to operate over an entire tree in top-down order, requiring success at every node" ]
   , external "anybu"      (anybuR :: RewriteH Core -> RewriteH Core)
       [ "promotes a rewrite to operate over an entire tree in bottom-up order, requiring success for at least one node" ]
   , external "anytd"      (anytdR :: RewriteH Core -> RewriteH Core)
       [ "promotes a rewrite to operate over an entire tree in top-down order, requiring success for at least one node" ]
   , external "alldu"      (allduR :: RewriteH Core -> RewriteH Core)
       [ "apply a rewrite twice, in a top-down and bottom-up way, using one single tree traversal",
         "succeeding if they all succeed"]
   , external "anydu"      (anyduR :: RewriteH Core -> RewriteH Core)
       [ "apply a rewrite twice, in a top-down and bottom-up way, using one single tree traversal",
         "succeeding if any succeed"]
   , external "tdprune"    (tdpruneR :: RewriteH Core -> RewriteH Core)
       [ "attempt to apply a rewrite in a top-down manner, prunning at successful rewrites" ]
   , external "innermost"  (innermostR :: RewriteH Core -> RewriteH Core)
       [ "a fixed-point traveral, starting with the innermost term" ]
   ]

------------------------------------------------------------------------------------
