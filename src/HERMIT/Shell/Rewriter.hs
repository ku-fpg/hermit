module HERMIT.Shell.Rewriter where
        
import HERMIT.Kure

class Rewriter r where
   toRewriteH :: r a -> RewriteH a
