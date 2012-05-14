module Language.HERMIT.Primitive.Kure where

import Language.KURE

import Language.HERMIT.HermitKure
import Language.HERMIT.External

------------------------------------------------------------------------------------

externals :: [External]
externals = 
   [ external "allbu"      (allbuR :: RewriteH Core -> RewriteH Core)
       [ "promotes a rewrite to operate over an entire tree in bottom-up order, requiring success at each node" ]
   , external "alltd"      (alltdR :: RewriteH Core -> RewriteH Core)
       [ "promotes a rewrite to operate over an entire tree in top-down order, requiring success at each node" ]
   , external "anybu"      (anybuR :: RewriteH Core -> RewriteH Core)
       [ "promotes a rewrite to operate over an entire tree in bottom-up order, requiring success for at least one node" ]
   , external "anytd"      (anytdR :: RewriteH Core -> RewriteH Core)
       [ "promotes a rewrite to operate over an entire tree in top-down order, requiring success for at least one node" ]
   , external "try"        (tryR :: RewriteH Core -> RewriteH Core)
       [ "tries a rewrite, and performs an identity if this rewrite fails" ]
   ]
   
------------------------------------------------------------------------------------
  