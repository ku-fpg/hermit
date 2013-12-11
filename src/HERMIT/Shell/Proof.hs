{-# LANGUAGE TypeFamilies, DeriveDataTypeable, FlexibleContexts #-}

module HERMIT.Shell.Proof where

import Control.Arrow
import qualified Control.Category as Cat
import Control.Monad.State

import Data.Dynamic

import HERMIT.Core
import HERMIT.External
import HERMIT.GHC
import HERMIT.Kernel.Scoped
import HERMIT.Kure
import HERMIT.Utilities

import HERMIT.Dictionary.Reasoning
import HERMIT.Dictionary.Rules

import HERMIT.PrettyPrinter.Common

import HERMIT.Shell.ScriptToRewrite
import HERMIT.Shell.Types

import qualified Language.Haskell.TH as TH

import System.IO

--------------------------------------------------------------------------------------------------------

externals :: [External]
externals =
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
        , "Prove a lemma by induction on the named identifier."
        , "Takes a list of proofs (in the form of scripts converting the LHS to the RHS) for each data constructor case,"
        , "in the same order as the given list of data constructor names."
        , "For example: inductive-proof \"LemmaAppendNil\" 'xs [ '[] , ': ] \"NilCaseScript\" \"ConsCaseScript\""
        , "The induction hypotheses are available for use under the names TODO"
        ]
    , external "inductive-proof-both-sides" (inductiveProofBothSidesExt :: TH.Name -> [TH.Name] -> [ScriptName] -> [ScriptName] -> ProofH)
        [ "inductive-proof-both-sides <lemma-name> <id-name> [<data-con-name>] [<script-name>] [<script-name>]"
        , "As inductive-proof, but takes scripts to apply to the RHS of each case as well as the LHS."
        ]
    , external "flip-proof" flipProof
        [ "Flip the LHS and RHS of a proof."
        , "Example usage: flip-proof (rewrite-to-proof r)"
        ]
    , external "rule-to-lemma" RuleToLemma
        [ "Create a lemma from a GHC RULE." ]
    , external "show-lemmas" ShowLemmas
        [ "List lemmas." ]
    , external "lemma" ((\s -> promoteExprBiR . lemma False s) :: CommandLineState -> LemmaName -> BiRewriteH Core)
        [ "Run an proven lemma as a bi-directional rewrite." ]
    , external "lemma-unsafe" ((\s -> promoteExprBiR . lemma True s) :: CommandLineState -> LemmaName -> BiRewriteH Core)
        [ "Run a lemma as a bi-directional rewrite." ]
    , external "verify-lemma" VerifyLemma
        [ "Prove a lemma." ]
    ]

--------------------------------------------------------------------------------------------------------

data ProofH = RewritingProof ScriptOrRewrite ScriptOrRewrite                                       -- | Prove by rewriting both sides to a common intermediate expression.
            | InductiveProof (Id -> Bool) [((DataCon -> Bool), ScriptOrRewrite, ScriptOrRewrite)]  -- | Prove by induction.

type ScriptOrRewrite = Either ScriptName (RewriteH CoreExpr) -- The named script should be convertible to a Rewrite.

--------------------------------------------------------------------------------------------------------

data ProofCommand
    = RuleToLemma RuleNameString
    | VerifyLemma LemmaName ProofH
    | ShowLemmas
--    | Induction LemmaName 
    deriving (Typeable)

instance Extern ProofCommand where
    type Box ProofCommand = ProofCommand
    box i = i
    unbox i = i

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

flipProof :: ProofH -> ProofH
flipProof (RewritingProof sr1 sr2)   = RewritingProof sr2 sr1
flipProof (InductiveProof pr cases)  = InductiveProof pr [ (dp,s2,s1) | (dp,s1,s2) <- cases ]

--------------------------------------------------------------------------------------------------------

getLemmaByName :: LemmaName -> CommandLineState -> Maybe Lemma
getLemmaByName nm st = 
    case [ lm | lm@(n,_,_) <- cl_lemmas st, n == nm ] of
        [] -> Nothing
        (l:_) -> Just l

lemma :: Bool -> CommandLineState -> LemmaName -> BiRewriteH CoreExpr
lemma ok st nm = 
    case getLemmaByName nm st of
        Nothing -> beforeBiR (fail $ "No lemma named: " ++ nm) (const Cat.id)
        Just (_,equality,proven) -> beforeBiR (guardMsg (proven || ok) $ "Lemma " ++ nm ++ " has not been proven.") (const $ birewrite equality)

--------------------------------------------------------------------------------------------------------

performProofCommand :: MonadIO m => ProofCommand -> CLM m ()
performProofCommand (RuleToLemma nm) = do
    st <- get
    equality <- queryS (cl_kernel st) (getSingletonHermitRuleT nm >>> ruleToEqualityT :: TranslateH Core CoreExprEquality) (cl_kernel_env st) (cl_cursor st)
    put $ st { cl_lemmas = (nm,equality,False) : cl_lemmas st }

performProofCommand (VerifyLemma nm proof) = do
    st <- get
    (_,equality,_) <- maybeM ("No lemma named: " ++ nm) (getLemmaByName nm st)
    prove equality proof -- this is like a guard
    markProven nm

performProofCommand ShowLemmas = do
    st <- get
    let k    = cl_kernel st
        env  = cl_kernel_env st
        sast = cl_cursor st
        pos  = cl_pretty_opts st
        pp   = cl_pretty st
        pr :: [Var] -> CoreExpr -> TranslateH CoreTC DocH
        pr vs e = return (mkCoreLams vs e) >>> extractT (pathT (replicate (length vs) Lam_Body) (liftPrettyH pos pp))
    forM_ (cl_lemmas st) $ \ (nm, CoreExprEquality vs lhs rhs, proven) -> do
        cl_putStr nm
        cl_putStrLn $ if proven then " (Proven)" else " (Not Proven)"
        unless (null vs) $ cl_putStrLn $ "forall " ++ unwords (map getOccString vs) ++ ". "
        lDoc <- queryS k (pr vs lhs) env sast
        rDoc <- queryS k (pr vs rhs) env sast
        liftIO $ cl_render st stdout pos (Right lDoc)
        cl_putStrLn "==>"
        liftIO $ cl_render st stdout pos (Right rDoc)

--------------------------------------------------------------------------------------------------------

-- | Prove a lemma using the given proof in the current kernel context.
-- Required to fail if proof fails.
prove :: MonadIO m => CoreExprEquality -> ProofH -> CLM m ()
prove equality (RewritingProof lp rp) = do
    lrr <- either (lookupScript >=> liftM extractR . scriptToRewrite) return lp
    rrr <- either (lookupScript >=> liftM extractR . scriptToRewrite) return rp
    st <- get
    queryS (cl_kernel st) (return equality >>> verifyCoreExprEqualityT (lrr, rrr) :: TranslateH CoreTC ()) (cl_kernel_env st) (cl_cursor st)
    
prove _ _ = fail "not yet implemented"

markProven :: MonadState CommandLineState m => LemmaName -> m ()
markProven nm = modify $ \ st -> st { cl_lemmas = [ (n,e, if n == nm then True else p) | (n,e,p) <- cl_lemmas st ] }
