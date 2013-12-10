{-# LANGUAGE TypeFamilies, DeriveDataTypeable #-}

module HERMIT.Shell.Proofs
  ()
where

import Data.Dynamic

import HERMIT.External
import HERMIT.GHC
import HERMIT.Kure

import HERMIT.Shell.Types

import qualified Language.Haskell.TH as TH

--------------------------------------------------------------------------------------------------------

proof_externals :: [External]
proof_externals =
   [ external "script-to-proof" scriptToProof
       [ "Convert a loaded script to an equality proof, by applying the script as a LHS to RHS rewrite." ]
   , external "script-both-sides-to-proof" scriptBothSidesToProof
       [ "Convert a pair of loaded scripts to a proof, by applying the first script to the LHS and the second script to the RHS." ]
   , external "rewrite-to-proof" (rewriteToProof . extractR :: RewriteH Core -> ProofH)
       [ "Convert a rewrite to an equality proof, by applying it to the LHS." ]
   , external "rewrite-both-sides-to-proof" ((\ r1 r2 -> rewriteBothSidesToProof (extractR r1) (extractR r2)) :: RewriteH Core -> RewriteH Core -> ProofH)
       [ "Convert a pair of rewrites to a proof, by applying the first rewrite to the LHS and the second rewrite to the RHS." ]
   , external "inductive-proof" (inductiveProofExt :: TH.Name -> [TH.Name] -> [ScriptName] -> ProofH)
      [ "inductive-proof <lemma-name> <id-name> [<data-con-name>] [<script-name>]"
      , "Prove a lemma by induction on the named identifier.",
        "Takes a list of proofs (in the form of scripts converting the LHS to the RHS) for each data constructor case,",
        "in the same order as the given list of data constructor names.",
        "For example: inductive-proof \"LemmaAppendNil\" 'xs [ '[] , ': ] \"NilCaseScript\" \"ConsCaseScript\"",
        "The induction hypotheses are available for use under the names TODO"
      ]
   , external "inductive-proof-both-sides" (inductiveProofBothSidesExt :: TH.Name -> [TH.Name] -> [ScriptName] -> [ScriptName] -> ProofH)
      [ "inductive-proof-both-sides <lemma-name> <id-name> [<data-con-name>] [<script-name>] [<script-name>]",
        "As inductive-proof, but takes scripts to apply to the RHS of each case as well as the LHS."
      ]
   ]

--------------------------------------------------------------------------------------------------------

data ProofH = RewritingProof ScriptOrRewrite ScriptOrRewrite                                       -- | Prove by rewriting both sides to a common intermediate expression.
            | InductiveProof (Id -> Bool) [((DataCon -> Bool), ScriptOrRewrite, ScriptOrRewrite)]  -- | Prove by induction.

type ScriptOrRewrite = Either ScriptName (RewriteH CoreExpr) -- The named script should be convertible to a Rewrite.

--------------------------------------------------------------------------------------------------------

data ProofBox = ProofBox ProofH deriving Typeable

instance Extern ProofH where
    type Box ProofH = ProofBox
    box = ProofBox
    unbox (ProofBox p) = p

--------------------------------------------------------------------------------------------------------

scriptToProof :: ScriptName -> ProofH
scriptToProof s = RewritingProof (Left s) (Right idR)

scriptBothSidesToProof :: ScriptName -> ScriptName -> ProofH
scriptBothSidesToProof s1 s2 = RewritingProof (Left s1) (Left s2)

rewriteToProof :: RewriteH CoreExpr -> ProofH
rewriteToProof r = RewritingProof (Right r) (Right idR)

rewriteBothSidesToProof :: RewriteH CoreExpr -> RewriteH CoreExpr -> ProofH
rewriteBothSidesToProof r1 r2 = RewritingProof (Right r1) (Right r2)

--------------------------------------------------------------------------------------------------------

inductiveProof :: (Id -> Bool) -> [((DataCon -> Bool), ScriptName)] -> ProofH
inductiveProof p cases = InductiveProof p (map (\ (dp,s) -> (dp, Left s, Right idR)) cases)

inductiveProofBothSides :: (Id -> Bool) -> [((DataCon -> Bool), ScriptName, ScriptName)] -> ProofH
inductiveProofBothSides p cases = InductiveProof p (map (\ (dp,s1,s2) -> (dp, Left s1, Left s2)) cases)

--------------------------------------------------------------------------------------------------------

-- inductiveProofExt :: TH.Name -> [(TH.Name, ScriptName)] -> ProofH
-- inductiveProofExt idn cases = inductiveProof (cmpTHName2Var idn) [ ((cmpTHName2Name dcn . dataConName), sn) | (dcn,sn) <- cases ]

-- TODO: Upgrade the parser so that this can be a list of pairs.
inductiveProofExt :: TH.Name -> [TH.Name] -> [ScriptName] -> ProofH
inductiveProofExt idn dcns sns = inductiveProof (cmpTHName2Var idn) (zip [ cmpTHName2Name dcn . dataConName | dcn <- dcns ] sns)

-- inductiveProofBothSidesExt :: TH.Name -> [(TH.Name, ScriptName, ScriptName)] -> ProofH
-- inductiveProofBothSidesExt idn cases = inductiveProofBothSides (cmpTHName2Var idn) [ ((cmpTHName2Name dcn . dataConName), sln, srn) | (dcn,sln,srn) <- cases ]

-- TODO: Upgrade the parser so that this can be a list of triples.
inductiveProofBothSidesExt :: TH.Name -> [TH.Name] -> [ScriptName] -> [ScriptName] -> ProofH
inductiveProofBothSidesExt idn dcns s1ns s2ns = inductiveProofBothSides (cmpTHName2Var idn) (zip3 [ cmpTHName2Name dcn . dataConName | dcn <- dcns ] s1ns s2ns)

--------------------------------------------------------------------------------------------------------
