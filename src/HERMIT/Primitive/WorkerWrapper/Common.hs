module HERMIT.Primitive.WorkerWrapper.Common where

import GhcPlugins as GHC hiding (varName)

import Control.Arrow

import HERMIT.Core
import HERMIT.Monad
import HERMIT.Kure
import HERMIT.External

import HERMIT.Primitive.New -- TODO: Sort out heirarchy

--------------------------------------------------------------------------------------------------

data WWAssumptionTag = A | B | C deriving (Eq,Ord,Show,Read)
data WWAssumption = WWAssumption WWAssumptionTag (RewriteH CoreExpr)

--------------------------------------------------------------------------------------------------

-- Note: The current approach to WW Fusion is a hack.
-- I'm not sure what the best way to approach this is though.
-- An alternative would be to have a generate command that adds ww-fusion to the dictionary, all preconditions verified in advance.
-- That would have to exist at the Shell level though.

-- This isn't entirely safe, as a malicious the user could define a label with this name.
workLabel :: Label
workLabel = "recursive-definition-of-work-for-use-by-ww-fusion"

--------------------------------------------------------------------------------------------------

parse2beforeBiR :: (CoreExpr -> CoreExpr -> BiRewriteH a) -> CoreString -> CoreString -> BiRewriteH a
parse2beforeBiR f s1 s2 = beforeBiR (parseCoreExprT s1 &&& parseCoreExprT s2) (uncurry f)

parse3beforeBiR :: (CoreExpr -> CoreExpr -> CoreExpr -> BiRewriteH a) -> CoreString -> CoreString -> CoreString -> BiRewriteH a
parse3beforeBiR f s1 s2 s3 = beforeBiR ((parseCoreExprT s1 &&& parseCoreExprT s2) &&& parseCoreExprT s3) ((uncurry.uncurry) f)

--------------------------------------------------------------------------------------------------

-- | Given two expressions, and a rewrite from the former to the latter, verify that rewrite.
verifyEqualityProofT :: CoreExpr -> CoreExpr -> RewriteH CoreExpr -> TranslateH a ()
verifyEqualityProofT sourceExpr targetExpr r =
  prefixFailMsg "equality verification failed: " $
  do resultExpr <- r <<< return sourceExpr
     guardMsg (exprAlphaEq targetExpr resultExpr) "result of running proof on lhs of equality does not match rhs of equality."

--------------------------------------------------------------------------------------------------
