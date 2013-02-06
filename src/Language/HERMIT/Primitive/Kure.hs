module Language.HERMIT.Primitive.Kure
       ( -- * KURE Strategies
         -- This list contains reflections of the KURE strategies as 'External's.
         externals
       )
where

import Control.Arrow

import Language.HERMIT.Core
import Language.HERMIT.Kure
import Language.HERMIT.External

------------------------------------------------------------------------------------

externals :: [External]
externals = map (.+ KURE)
   [ external "id"         (idR :: RewriteH Core)
       [ "perform the identity"] .+ Shallow
   , external "fail"       (fail :: String -> RewriteH Core)
       [ "a failing rewrite"]
   , external "<+"         ((<+) :: RewriteH Core -> RewriteH Core -> RewriteH Core)
       [ "perform the first translate, and then, if it fails, perform the second rewrite" ]
   , external ">>>"        ((>>>) :: RewriteH Core -> RewriteH Core -> RewriteH Core)
       [ "compose rewrites, requiring both to succeed" ]
   , external ">>>"        ((>>>) :: BiRewriteH Core -> BiRewriteH Core -> BiRewriteH Core)
       [ "compose bidirectional rewrites, requiring both to succeed" ]
   , external ">+>"        ((>+>) :: RewriteH Core -> RewriteH Core -> RewriteH Core)
       [ "compose rewrites, allowing one to fail" ]
   , external "try"        (tryR :: RewriteH Core -> RewriteH Core)
       [ "tries a rewrite, and performs an identity if this rewrite fails" ]
   , external "repeat"     (repeatR :: RewriteH Core -> RewriteH Core)
       [ "repeats a rewrite until it would fail" ] .+ Loop
   , external "all"        (allR :: RewriteH Core -> RewriteH Core)
       [ "apply a rewrite to all children of the node, requiring success at every child" ] .+ Shallow
   , external "any"        (anyR :: RewriteH Core -> RewriteH Core)
       [ "apply a rewrite to all children of the node, requiring success for at least one child" ] .+ Shallow
   , external "one"        (oneR :: RewriteH Core -> RewriteH Core)
       [ "apply a rewrite to the first child of the node for which it can succeed" ] .+ Shallow
   , external "all-bu"     (allbuR :: RewriteH Core -> RewriteH Core)
       [ "promotes a rewrite to operate over an entire tree in bottom-up order, requiring success at each node" ] .+ Deep
   , external "all-td"     (alltdR :: RewriteH Core -> RewriteH Core)
       [ "promotes a rewrite to operate over an entire tree in top-down order, requiring success at every node" ] .+ Deep
   , external "all-du"     (allduR :: RewriteH Core -> RewriteH Core)
       [ "apply a rewrite twice, in a top-down and bottom-up way, using one single tree traversal",
         "succeeding if they all succeed"] .+ Deep
   , external "any-bu"     (anybuR :: RewriteH Core -> RewriteH Core)
       [ "promotes a rewrite to operate over an entire tree in bottom-up order, requiring success for at least one node" ] .+ Deep
   , external "any-td"     (anytdR :: RewriteH Core -> RewriteH Core)
       [ "promotes a rewrite to operate over an entire tree in top-down order, requiring success for at least one node" ] .+ Deep
   , external "any-du"     (anyduR :: RewriteH Core -> RewriteH Core)
       [ "apply a rewrite twice, in a top-down and bottom-up way, using one single tree traversal",
         "succeeding if any succeed"] .+ Deep
   , external "one-td"     (onetdR :: RewriteH Core -> RewriteH Core)
       [ "applies a rewrite to the first node (in a top-down order) for which it can succeed" ] .+ Deep
   , external "one-bu"     (onebuR :: RewriteH Core -> RewriteH Core)
       [ "applies a rewrite to the first node (in a bottom-up order) for which it can succeed" ] .+ Deep
   , external "prune-td"   (prunetdR :: RewriteH Core -> RewriteH Core)
       [ "attempt to apply a rewrite in a top-down manner, prunning at successful rewrites" ] .+ Deep
   , external "innermost"  (innermostR :: RewriteH Core -> RewriteH Core)
       [ "a fixed-point traveral, starting with the innermost term" ] .+ Deep .+ Loop
   , external "focus"      (hfocusR :: TranslateH Core Path -> RewriteH Core -> RewriteH Core)
       [ "apply a rewrite to a focal point"] .+ Navigation .+ Deep
   , external "focus"      (hfocusT :: TranslateH Core Path -> TranslateH Core String -> TranslateH Core String)
       [ "apply a query at a focal point"] .+ Navigation .+ Deep
   , external "when"       ((>>) :: TranslateH Core () -> RewriteH Core -> RewriteH Core)
       [ "apply a rewrite only if the check succeeds" ] .+ Predicate
   , external "not"        (notM :: TranslateH Core () -> TranslateH Core ())
       [ "cause a failing check to succeed, a succeeding check to fail" ] .+ Predicate
   , external "invert"     (invertBiT :: BiRewriteH Core -> BiRewriteH Core)
       [ "reverse a bidirectional rewrite" ]
   , external "foreward"   (forewardT :: BiRewriteH Core -> RewriteH Core)
       [ "apply a bidirectional rewrite forewards" ]
   , external "backward"   (backwardT :: BiRewriteH Core -> RewriteH Core)
       [ "apply a bidirectional rewrite backwards" ]
   ]

------------------------------------------------------------------------------------

hfocusR :: TranslateH Core Path -> RewriteH Core -> RewriteH Core
hfocusR tp r = do p <- tp
                  pathR p r

hfocusT :: TranslateH Core Path -> TranslateH Core String -> TranslateH Core String
hfocusT tp t = do p <- tp
                  pathT p t

------------------------------------------------------------------------------------
