module HERMIT.Shell.Proofs where

import HERMIT.GHC
import HERMIT.Kure

import HERMIT.Shell.Types

--------------------------------------------------------------------------------------------------------

data ProofH = RewritingProof ScriptOrRewrite ScriptOrRewrite                                       -- | Prove by rewriting both sides to a common intermediate expression.
            | InductiveProof (Id -> Bool) [((DataCon -> Bool), ScriptOrRewrite, ScriptOrRewrite)]  -- | Prove by induction.

type ScriptOrRewrite = Either ScriptName (RewriteH CoreExpr) -- The named script should be convertible to a Rewrite.

--------------------------------------------------------------------------------------------------------

scriptToProof :: ScriptName -> ProofH
scriptToProof s = RewritingProof (Left s) (Right idR)

scriptBothSidesToProof :: ScriptName -> ScriptName -> ProofH
scriptBothSidesToProof s1 s2 = RewritingProof (Left s1) (Left s2)

rewriteToProof :: RewriteH CoreExpr -> ProofH
rewriteToProof r = RewritingProof (Right r) (Right idR)

rewriteBothSidesToProof :: RewriteH CoreExpr -> RewriteH CoreExpr -> ProofH
rewriteBothSidesToProof r1 r2 = RewritingProof (Right r1) (Right r2)

inductiveProof :: (Id -> Bool) -> [((DataCon -> Bool), ScriptName)] -> ProofH
inductiveProof p cases = InductiveProof p (map (\ (dp,s) -> (dp, Left s, Right idR)) cases)

inductiveProofBothSides :: (Id -> Bool) -> [((DataCon -> Bool), ScriptName, ScriptName)] -> ProofH
inductiveProofBothSides p cases = InductiveProof p (map (\ (dp,s1,s2) -> (dp, Left s1, Left s2)) cases)

--------------------------------------------------------------------------------------------------------
