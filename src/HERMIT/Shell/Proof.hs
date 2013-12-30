{-# LANGUAGE TypeFamilies, DeriveDataTypeable, FlexibleContexts, ScopedTypeVariables #-}

module HERMIT.Shell.Proof where

import Control.Arrow
import qualified Control.Category as Cat
import Control.Monad.Error
import Control.Monad.State

import Data.Dynamic
import Data.List

import HERMIT.Core
import HERMIT.External
import HERMIT.GHC
import HERMIT.Kernel.Scoped
import HERMIT.Kure
import HERMIT.Utilities

import HERMIT.Dictionary.Common
import HERMIT.Dictionary.Debug
import HERMIT.Dictionary.Induction
import HERMIT.Dictionary.Reasoning
import HERMIT.Dictionary.Rules

import HERMIT.PrettyPrinter.Common
import qualified HERMIT.PrettyPrinter.Clean as Clean

import HERMIT.Shell.ScriptToRewrite
import HERMIT.Shell.Types

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
    , external "inductive-proof" (inductiveProofExt :: String -> [String] -> [ScriptName] -> ProofH)
        [ "inductive-proof <id-name> [<data-con-name>] [<script-name>]"
        , "Build an equality proof by induction on the named identifier."
        , "Takes a list of proofs (in the form of scripts converting the LHS to the RHS) for each data constructor case,"
        , "in the same order as the given list of data constructor names."
        , "For example: inductive-proof 'xs [ '[] , ': ] [ \"NilCaseScript\" , \"ConsCaseScript\" ]"
        , "The induction hypotheses are available for use under the names ind-hyp-0, ind-hyp-1, etc..."
        ]
    , external "inductive-proof-both-sides" (inductiveProofBothSidesExt :: String -> [String] -> [ScriptName] -> [ScriptName] -> ProofH)
        [ "inductive-proof-both-sides <id-name> [<data-con-name>] [<script-name>] [<script-name>]"
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

-- inductiveProofExt :: String -> [(String, ScriptName)] -> ProofH
-- inductiveProofExt idn cases = inductiveProof (cmpString2Var idn) [ ((cmpString2Name dcn . dataConName), sn) | (dcn,sn) <- cases ]

-- TODO: Upgrade the parser so that this can be a list of pairs.
inductiveProofExt :: String -> [String] -> [ScriptName] -> ProofH
inductiveProofExt idn dcns sns = inductiveProof (cmpString2Var idn) (zip [ cmpString2Name dcn . dataConName | dcn <- dcns ] sns)

-- inductiveProofBothSidesExt :: String -> [(String, ScriptName, ScriptName)] -> ProofH
-- inductiveProofBothSidesExt idn cases = inductiveProofBothSides (cmpString2Var idn) [ ((cmpString2Name dcn . dataConName), sln, srn) | (dcn,sln,srn) <- cases ]

-- TODO: Upgrade the parser so that this can be a list of triples.
inductiveProofBothSidesExt :: String -> [String] -> [ScriptName] -> [ScriptName] -> ProofH
inductiveProofBothSidesExt idn dcns s1ns s2ns = inductiveProofBothSides (cmpString2Var idn) (zip3 [ cmpString2Name dcn . dataConName | dcn <- dcns ] s1ns s2ns)

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

performProofCommand ShowLemmas = gets cl_lemmas >>= \ ls -> forM_ (reverse ls) printLemma

printLemma :: MonadIO m => Lemma -> CLM m ()
printLemma (nm, CoreExprEquality bs lhs rhs, proven) = do
    st <- get
    let k    = cl_kernel st
        env  = cl_kernel_env st
        sast = cl_cursor st
        pos  = cl_pretty_opts st
        pp   = cl_pretty st
        pr :: [Var] -> CoreExpr -> TranslateH Core DocH
        pr vs e = return e >>> withVarsInScope vs (extractT $ liftPrettyH pos pp)
    cl_putStr nm
    cl_putStrLn $ if proven then " (Proven)" else " (Not Proven)"
    unless (null bs) $ do
        forallDoc <- queryS k (return bs >>> extractT (liftPrettyH pos Clean.ppForallQuantification) :: TranslateH Core DocH) env sast -- TODO: rather than hardwiring the Clean PP here, we should store a pretty printer in the shell state, which should match the main PP, and be updated correspondingly.
        liftIO $ cl_render st stdout pos (Right forallDoc)
    lDoc <- queryS k (pr bs lhs) env sast
    rDoc <- queryS k (pr bs rhs) env sast
    liftIO $ cl_render st stdout pos (Right lDoc)
    cl_putStrLn "=="
    liftIO $ cl_render st stdout pos (Right rDoc)
    cl_putStrLn ""

--------------------------------------------------------------------------------------------------------

-- | Prove a lemma using the given proof in the current kernel context.
-- Required to fail if proof fails.
prove :: MonadIO m => CoreExprEquality -> ProofH -> CLM m ()
prove equality (RewritingProof lp rp) = do
    (lrr, rrr) <- getRewrites (lp, rp)
    st <- get
    queryS (cl_kernel st) (return equality >>> verifyCoreExprEqualityT (lrr, rrr) :: TranslateH Core ()) (cl_kernel_env st) (cl_cursor st)

-- InductiveProof (Id -> Bool) [((DataCon -> Bool), ScriptOrRewrite, ScriptOrRewrite)]
-- inductionOnT :: forall c. (AddBindings c, ReadBindings c, ReadPath c Crumb, ExtendPath c Crumb, Walker c Core)
--              => (Id -> Bool)
--              -> (DataCon -> [BiRewrite c HermitM CoreExpr] -> CoreExprEqualityProof c HermitM)
--              -> Translate c HermitM CoreExprEquality ()
prove eq@(CoreExprEquality bs lhs rhs) (InductiveProof idPred caseProofs) = do
    st <- get

    i <- setFailMsg "specified identifier is not universally quantified in this equality lemma." $ soleElement (filter idPred bs)
    cases <- queryS (cl_kernel st) (inductionCaseSplit bs i lhs rhs :: TranslateH Core [(DataCon,[Var],CoreExpr,CoreExpr)]) (cl_kernel_env st) (cl_cursor st)

    forM_ cases $ \ (dc,vs,lhsE,rhsE) -> do

        (lp,rp) <- getProofsForCase dc caseProofs

        let vs_matching_i_type = filter (typeAlphaEq (varType i) . varType) vs
            -- Generate list of specialized induction hypotheses for the recursive cases.
            eqs = [ discardUniVars $ instantiateCoreExprEqVar i (Var i') eq
                  | i' <- vs_matching_i_type ]
            brs = map birewrite eqs
            nms = [ "ind-hyp-" ++ show n | n :: Int <- [0..] ]

        forM_ [ (nm, e, True) | (nm,e) <- zip nms eqs ] printLemma
        catchError (do put $ addToDict (zip nms brs) st
                       (l,r) <- getRewrites (lp,rp)
                       prove (CoreExprEquality (delete i bs ++ vs) lhsE rhsE) (rewriteBothSidesToProof l r) -- recursion!
                   )
                   (\ err -> put st >> throwError err)
        put st -- put original state (with original dictionary) back

getProofsForCase :: Monad m => DataCon -> [(DataCon -> Bool, ScriptOrRewrite, ScriptOrRewrite)] -> m (ScriptOrRewrite, ScriptOrRewrite)
getProofsForCase dc cases = case [ (l,r) | (dcPred, l, r) <- cases, dcPred dc ] of
                                [] -> fail $ "no case for " ++ getOccString dc
                                [p] -> return p
                                _ -> fail $ "more than one case for " ++ getOccString dc

addToDict :: [(String, BiRewriteH CoreExpr)] -> CommandLineState -> CommandLineState
addToDict rs st = st { cl_dict = foldr (\ (nm,r) -> addToDictionary (external nm (promoteExprBiR (beforeBiR (observeR ("Applying " ++ nm ++ " to: ")) (const r)) :: BiRewriteH Core) [])) (cl_dict st) rs }

{-
       let verifyInductiveCaseT :: (DataCon,[Var],CoreExpr,CoreExpr) -> Translate c HermitM x ()
           verifyInductiveCaseT (con,vs,lhsE,rhsE) =
                let vs_matching_i_type = filter (typeAlphaEq (varType i) . varType) vs
                    eqs = [ discardUniVars (instantiateCoreExprEq [(i,Var i')] eq) | i' <- vs_matching_i_type ]
                    brs = map birewrite eqs -- These eqs now have no universally quantified variables.
                                            -- Thus they can only be used on variables in the induction hypothesis.
                                            -- TODO: consider whether this is unneccassarily restrictive
                    caseEq = CoreExprEquality (delete i bs ++ vs) lhsE rhsE
                in return caseEq >>> verifyCoreExprEqualityT (genCaseAltProofs con brs)

       mapM_ verifyInductiveCaseT cases
-}

getRewrites :: MonadState CommandLineState m => (ScriptOrRewrite, ScriptOrRewrite) -> m (RewriteH CoreExpr, RewriteH CoreExpr)
getRewrites (l,r) = liftM2 (,) (getRewrite l) (getRewrite r)

getRewrite :: MonadState CommandLineState m => ScriptOrRewrite -> m (RewriteH CoreExpr)
getRewrite = either (lookupScript >=> liftM extractR . scriptToRewrite) return

markProven :: MonadState CommandLineState m => LemmaName -> m ()
markProven nm = modify $ \ st -> st { cl_lemmas = [ (n,e, if n == nm then True else p) | (n,e,p) <- cl_lemmas st ] }
