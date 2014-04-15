{-# LANGUAGE TypeFamilies, DeriveDataTypeable, FlexibleContexts, ScopedTypeVariables #-}

module HERMIT.Shell.Proof where

import Control.Arrow hiding (loop)
import Control.Concurrent
import Control.Monad.Error
import Control.Monad.State

import Data.Char (isSpace)
import Data.Dynamic
import Data.List
import Data.Maybe (isNothing)

import HERMIT.Core
import HERMIT.External
import HERMIT.GHC hiding (settings)
import HERMIT.Kernel.Scoped
import HERMIT.Kure
import HERMIT.Parser
import HERMIT.Utilities

import HERMIT.Dictionary.Common
import HERMIT.Dictionary.Debug
import HERMIT.Dictionary.Induction
import HERMIT.Dictionary.Reasoning
import HERMIT.Dictionary.Rules

import HERMIT.Plugin.Types
import HERMIT.PrettyPrinter.Common
import qualified HERMIT.PrettyPrinter.Clean as Clean

import HERMIT.Shell.Interpreter
import HERMIT.Shell.ScriptToRewrite
import HERMIT.Shell.Types

import System.Console.Haskeline hiding (catch, display)

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
    , external "lemma-to-proof" lemmaToProof
        [ "Convert a (proven) lemma to an equality proof." ]
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
        [ "Generate a bi-directional rewrite from a proven lemma." ]
    , external "lemma-unsafe" ((\s -> promoteExprBiR . lemma True s) :: CommandLineState -> LemmaName -> BiRewriteH Core)
        [ "Generate a bi-directional rewrite from a lemma, even if it is unproven." ]
    , external "verify-lemma" VerifyLemma
        [ "Prove a lemma." ]
    , external "lemma-lhs-intro" (lemmaLhsIntroR :: CommandLineState -> LemmaName -> RewriteH Core)
        [ "Introduce the LHS of a lemma as a non-recursive binding, in either an expression or a program."
        , "body ==> let v = lhs in body" ] .+ Introduce .+ Shallow
    , external "lemma-rhs-intro" (lemmaRhsIntroR :: CommandLineState -> LemmaName -> RewriteH Core)
        [ "Introduce the RHS of a lemma as a non-recursive binding, in either an expression or a program."
        , "body ==> let v = rhs in body" ] .+ Introduce .+ Shallow
    , external "interactive-proof" InteractiveProof
        [ "Proof a lemma interactively." ]
    , external "abandon" PCAbort
        [ "Abandon interactive proof attempt." ]
    , external "extensionality" (PCApply . extensionalityR . Just :: String -> ProofCmd)
        [ "Given a name 'x, then"
        , "f == g  ==>  forall x.  f x == g x" ]
    , external "extensionality" (PCApply $ extensionalityR Nothing :: ProofCmd)
        [ "f == g  ==>  forall x.  f x == g x" ]
    , external "lhs" (PCApply . lhsR . extractR :: RewriteH Core -> ProofCmd)
        [ "Apply a rewrite to the LHS of an equality." ]
    , external "rhs" (PCApply . rhsR . extractR :: RewriteH Core -> ProofCmd)
        [ "Apply a rewrite to the RHS of an equality." ]
    , external "both" (PCApply . bothR . extractR :: RewriteH Core -> ProofCmd)
        [ "Apply a rewrite to both sides of an equality." ]
    ]

--------------------------------------------------------------------------------------------------------

data ProofH = RewritingProof ScriptOrRewrite ScriptOrRewrite                                             -- ^ Prove by rewriting both sides to a common intermediate expression.
            | InductiveProof (Id -> Bool) [((Maybe DataCon -> Bool), ScriptOrRewrite, ScriptOrRewrite)]  -- ^ Prove by induction.  'Nothing' is the 'undefined' case.
            | UserProof (TransformH CoreExprEquality ())                                                 -- ^ A user-defined proof technique.
            | ProofH (CoreExprEquality -> CLT IO ())                                                     -- ^ User-defined proof with full access to shell monad stack.

type ScriptOrRewrite = Either ScriptName (RewriteH CoreExpr) -- The named script should be convertible to a Rewrite.

--------------------------------------------------------------------------------------------------------

data ProofCommand
    = RuleToLemma RuleNameString
    | VerifyLemma LemmaName ProofH
    | InteractiveProof LemmaName
    | ShowLemmas
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

-- | Verify an equality by applying a user-supplied predicate.
--   If the predicate holds, HERMIT accepts the equality as proven.
userProofTechnique :: TransformH CoreExprEquality () -> ProofH
userProofTechnique = UserProof

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

inductiveProof :: (Id -> Bool) -> [((Maybe DataCon -> Bool), ScriptName)] -> ProofH
inductiveProof p cases = InductiveProof p (map (\ (dp,s) -> (dp, Left s, Right idR)) cases)

inductiveProofBothSides :: (Id -> Bool) -> [((Maybe DataCon -> Bool), ScriptName, ScriptName)] -> ProofH
inductiveProofBothSides p cases = InductiveProof p (map (\ (dp,s1,s2) -> (dp, Left s1, Left s2)) cases)

--------------------------------------------------------------------------------------------------------

-- inductiveProofExt :: String -> [(String, ScriptName)] -> ProofH
-- inductiveProofExt idn cases = inductiveProof (cmpString2Var idn) [ ((cmpString2Name dcn . dataConName), sn) | (dcn,sn) <- cases ]

-- TODO: Upgrade the parser so that this can be a list of pairs.
inductiveProofExt :: String -> [String] -> [ScriptName] -> ProofH
inductiveProofExt idn dcns sns = inductiveProof (cmpString2Var idn) (zip (caseNamePreds dcns) sns)

-- inductiveProofBothSidesExt :: String -> [(String, ScriptName, ScriptName)] -> ProofH
-- inductiveProofBothSidesExt idn cases = inductiveProofBothSides (cmpString2Var idn) [ ((cmpString2Name dcn . dataConName), sln, srn) | (dcn,sln,srn) <- cases ]

-- TODO: Upgrade the parser so that this can be a list of triples.
inductiveProofBothSidesExt :: String -> [String] -> [ScriptName] -> [ScriptName] -> ProofH
inductiveProofBothSidesExt idn dcns s1ns s2ns = inductiveProofBothSides (cmpString2Var idn) (zip3 (caseNamePreds dcns) s1ns s2ns)

-- isNothing for the undefined case
caseNamePreds :: [String] -> [Maybe DataCon -> Bool]
caseNamePreds dcns = isNothing : [ maybe False (cmpString2Name dcn . dataConName) | dcn <- dcns ]

--------------------------------------------------------------------------------------------------------

flipProof :: ProofH -> ProofH
flipProof (RewritingProof sr1 sr2)   = RewritingProof sr2 sr1
flipProof (InductiveProof pr cases)  = InductiveProof pr [ (dp,s2,s1) | (dp,s1,s2) <- cases ]
flipProof (UserProof t)              = UserProof (arr flipCoreExprEquality >>> t)
flipProof (ProofH p)                 = ProofH (p . flipCoreExprEquality)

--------------------------------------------------------------------------------------------------------

getLemmaByName :: Monad m => CommandLineState -> LemmaName -> m Lemma
getLemmaByName st nm =
    case [ lm | lm@(n,_,_) <- cl_lemmas st, n == nm ] of
        []    -> fail ("No lemma named: " ++ nm)
        (l:_) -> return l

lemma :: Bool -> CommandLineState -> LemmaName -> BiRewriteH CoreExpr
lemma ok st nm = beforeBiR
                   (do (_,equality,proven) <- getLemmaByName st nm
                       guardMsg (proven || ok) ("Lemma " ++ nm ++ " has not been proven.")
                       return equality
                   )
                   birewrite

lemmaToProof :: CommandLineState -> LemmaName -> ProofH
lemmaToProof st nm = rewriteToProof (forwardT (lemma False st nm))

--------------------------------------------------------------------------------------------------------

lemmaNameToEqualityT :: Monad m => CommandLineState -> LemmaName -> m CoreExprEquality
lemmaNameToEqualityT st nm =
  do (_,eq,_) <- getLemmaByName st nm
     return eq

-- | @e@ ==> @let v = lhs in e@  (also works in a similar manner at Program nodes)
lemmaLhsIntroR :: CommandLineState -> LemmaName -> RewriteH Core
lemmaLhsIntroR st = lemmaNameToEqualityT st >=> eqLhsIntroR

-- | @e@ ==> @let v = rhs in e@  (also works in a similar manner at Program nodes)
lemmaRhsIntroR :: CommandLineState -> LemmaName -> RewriteH Core
lemmaRhsIntroR st = lemmaNameToEqualityT st >=> eqRhsIntroR

--------------------------------------------------------------------------------------------------------

performProofCommand :: MonadIO m => ProofCommand -> CLT m ()
performProofCommand (RuleToLemma nm) = do
    st <- gets cl_pstate
    equality <- queryS (ps_kernel st) (ruleNameToEqualityT nm :: TransformH Core CoreExprEquality) (mkKernelEnv st) (ps_cursor st)
    modify $ \ s -> s { cl_lemmas = (nm,equality,False) : cl_lemmas s }

performProofCommand (VerifyLemma nm proof) = do
    st <- get
    (_,equality,_) <- getLemmaByName st nm
    prove equality proof -- this is like a guard
    markProven nm

performProofCommand (InteractiveProof nm) = get >>= flip getLemmaByName nm >>= interactiveProof 

performProofCommand ShowLemmas = gets cl_lemmas >>= \ ls -> forM_ (reverse ls) printLemma

printLemma :: MonadIO m => Lemma -> CLT m ()
printLemma (nm, CoreExprEquality bs lhs rhs, proven) = do
    st <- gets cl_pstate
    let k    = ps_kernel st
        env  = mkKernelEnv st
        sast = ps_cursor st
        pos  = ps_pretty_opts st
        pp   = ps_pretty st
        pr :: [Var] -> CoreExpr -> TransformH Core DocH
        pr vs e = return e >>> withVarsInScope vs (extractT $ liftPrettyH pos pp)
    cl_putStr nm
    cl_putStrLn $ if proven then " (Proven)" else " (Not Proven)"
    unless (null bs) $ do
        forallDoc <- queryS k (return bs >>> extractT (liftPrettyH pos Clean.ppForallQuantification) :: TransformH Core DocH) env sast -- TODO: rather than hardwiring the Clean PP here, we should store a pretty printer in the shell state, which should match the main PP, and be updated correspondingly.
        liftIO $ ps_render st stdout pos (Right forallDoc)
    lDoc <- queryS k (pr bs lhs) env sast
    rDoc <- queryS k (pr bs rhs) env sast
    liftIO $ ps_render st stdout pos (Right lDoc)
    cl_putStrLn "=="
    liftIO $ ps_render st stdout pos (Right rDoc)
    cl_putStrLn ""

--------------------------------------------------------------------------------------------------------

-- | Prove a lemma using the given proof in the current kernel context.
-- Required to fail if proof fails.
prove :: MonadIO m => CoreExprEquality -> ProofH -> CLT m ()
prove eq (RewritingProof lp rp) = do
    (lrr, rrr) <- getRewrites (lp, rp)
    st <- gets cl_pstate
    queryS (ps_kernel st) (return eq >>> proveCoreExprEqualityT (lrr, rrr) :: TransformH Core ()) (mkKernelEnv st) (ps_cursor st)

-- InductiveProof (Id -> Bool) [((DataCon -> Bool), ScriptOrRewrite, ScriptOrRewrite)]
-- inductionOnT :: forall c. (AddBindings c, ReadBindings c, ReadPath c Crumb, ExtendPath c Crumb, Walker c Core)
--              => (Id -> Bool)
--              -> (DataCon -> [BiRewrite c HermitM CoreExpr] -> CoreExprEqualityProof c HermitM)
--              -> Transform c HermitM CoreExprEquality ()
prove eq@(CoreExprEquality bs lhs rhs) (InductiveProof idPred caseProofs) = do
    st <- get
    let ps = cl_pstate st

    i <- setFailMsg "specified identifier is not universally quantified in this equality lemma." $ soleElement (filter idPred bs)
    cases <- queryS (ps_kernel ps) (inductionCaseSplit bs i lhs rhs :: TransformH Core [(Maybe DataCon,[Var],CoreExpr,CoreExpr)]) (mkKernelEnv ps) (ps_cursor ps)

    forM_ cases $ \ (mdc,vs,lhsE,rhsE) -> do

        (lp,rp) <- getProofsForCase mdc caseProofs

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

prove eq (UserProof t) =
  do st <- gets cl_pstate
     queryS (ps_kernel st) (return eq >>> t :: TransformH Core ()) (mkKernelEnv st) (ps_cursor st)

prove eq (ProofH p) = clm2clt (p eq)

getProofsForCase :: Monad m => Maybe DataCon -> [(Maybe DataCon -> Bool, ScriptOrRewrite, ScriptOrRewrite)] -> m (ScriptOrRewrite, ScriptOrRewrite)
getProofsForCase mdc cases =
  let dcnm = maybe "undefined" getOccString mdc
   in case [ (l,r) | (dcPred, l, r) <- cases, dcPred mdc ] of
        []  -> fail $ "no case for " ++ dcnm
        [p] -> return p
        _   -> fail $ "more than one case for " ++ dcnm

addToDict :: [(String, BiRewriteH CoreExpr)] -> CommandLineState -> CommandLineState
addToDict rs st = st { cl_dict = foldr (\ (nm,r) -> addToDictionary (external nm (promoteExprBiR (beforeBiR (observeR ("Applying " ++ nm ++ " to: ")) (const r)) :: BiRewriteH Core) [])) (cl_dict st) rs }

{-
       let verifyInductiveCaseT :: (DataCon,[Var],CoreExpr,CoreExpr) -> Transform c HermitM x ()
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
markProven nm = do
    cl_putStrLn $ "Successfully proven: " ++ nm
    modify $ \ st -> st { cl_lemmas = [ (n,e, if n == nm then True else p) | (n,e,p) <- cl_lemmas st ] }

interactiveProof :: MonadIO m => Lemma -> CLT m ()
interactiveProof lem = do
    -- TODO: add any interactive-proof-specific commands to the dictionary?
    -- modify $ \ st -> st { cl_dict = mkDict (shell_externals ++ exts) }
    clState <- get
    completionMVar <- liftIO $ newMVar clState

    let ws_complete = " ()"

        -- To decide whether to continue the proof or not.
        loopUnproven :: Lemma -> CLT (InputT IO) ()
        loopUnproven l@(nm, eq, _) = do
            st <- get

            let sk = cl_kernel st
                kEnv = cl_kernel_env st
                sast = cl_cursor st

            -- Why do a query? We want to do our proof in the current context of the shell, whatever that is.
            ifM (queryS sk (return eq >>> testM verifyCoreExprEqualityT :: TransformH Core Bool) kEnv sast)
                (markProven nm)
                (loop l)

        -- Main proof input loop
        loop :: Lemma -> CLT (InputT IO) ()
        loop l = do
            printLemma l
            st <- get
            liftIO $ modifyMVar_ completionMVar (const $ return st) -- so the completion can get the current state
            mLine <- lift $ getInputLine $ "proof> "

            case mLine of
                Nothing          -> fail "proof aborted (input: Nothing)"
                Just ('-':'-':_) -> loop l
                Just line        -> if all isSpace line
                                    then loop l
                                    else do (er, st') <- runCLT st (evalProofScript l line `catchM` (\msg -> cl_putStrLn msg >> return l))
                                            case er of
                                                Right l' -> put st' >> loopUnproven l'
                                                Left CLAbort -> return ()
                                                Left _ -> fail "unsupported exception in interactive prover"

    -- Display a proof banner?

    -- Start the CLI
    let settings = setComplete (completeWordWithPrev Nothing ws_complete (shellComplete completionMVar)) defaultSettings
    (r,s) <- get >>= liftIO . runInputTBehavior defaultBehavior settings . flip runCLT (loop lem)
    either throwError (\v -> put s >> return v) r

evalProofScript :: MonadIO m => Lemma -> String -> CLT m Lemma
evalProofScript lem = parseScriptCLT >=> foldM runProofExprH lem

runProofExprH :: MonadIO m => Lemma -> ExprH -> CLT m Lemma
runProofExprH lem@(nm, eq, b) expr = prefixFailMsg ("Error in expression: " ++ unparseExprH expr ++ "\n") $ do
    cmd <- interpExprH interpProof expr
    st <- get
    case cmd of
        PCApply rr -> do
            let sk = cl_kernel st
                kEnv = cl_kernel_env st
                sast = cl_cursor st

            -- Why do a query? We want to do our proof in the current context of the shell, whatever that is.
            eq' <- queryS sk (return eq >>> rr :: TransformH Core CoreExprEquality) kEnv sast
            return (nm, eq', b)
        PCAbort -> throwError CLAbort -- we'll catch this specially
        PCUnsupported s -> cl_putStrLn s >> return lem

data ProofCmd = PCApply (RewriteH CoreExprEquality)
              | PCAbort
              | PCUnsupported String
    deriving Typeable

instance Extern ProofCmd where
    type Box ProofCmd = ProofCmd
    box i = i
    unbox i = i



interpProof :: [Interp ProofCmd]
interpProof =
  [ interp $ \ (RewriteCoreBox rr)            -> PCApply $ bothR $ extractR rr
  , interp $ \ (RewriteCoreTCBox rr)          -> PCApply $ bothR $ extractR rr
  , interp $ \ (BiRewriteCoreBox br)          -> PCApply $ bothR $ (extractR (forwardT br) <+ extractR (backwardT br))
  , interp $ \ (CrumbBox _cr)                 -> PCUnsupported "CrumbBox"
  , interp $ \ (PathBox _p)                   -> PCUnsupported "PathBox"
  , interp $ \ (TransformCorePathBox _tt)     -> PCUnsupported "TransformCorePathBox"
  , interp $ \ (TransformCoreTCPathBox _tt)   -> PCUnsupported "TransformCoreTCPathBox"
  , interp $ \ (StringBox _str)               -> PCUnsupported "StringBox"
  , interp $ \ (TransformCoreStringBox _tt)   -> PCUnsupported "TransformCoreStringBox"
  , interp $ \ (TransformCoreTCStringBox _tt) -> PCUnsupported "TransformCoreTCStringBox"
  , interp $ \ (TransformCoreTCDocHBox _tt)   -> PCUnsupported "TransformCoreTCDocHBox"
  , interp $ \ (TransformCoreCheckBox _tt)    -> PCUnsupported "TransformCoreCheckBox"
  , interp $ \ (TransformCoreTCCheckBox _tt)  -> PCUnsupported "TransformCoreTCCheckBox"
  , interp $ \ (_effect :: KernelEffect)      -> PCUnsupported "KernelEffect"
  , interp $ \ (_effect :: ShellEffect)       -> PCUnsupported "ShellEffect"
  , interp $ \ (_query :: QueryFun)           -> PCUnsupported "QueryFun"
  , interp $ \ (_cmd :: ProofCommand)         -> PCUnsupported "ProofCommand Inception!"
  , interp $ \ (cmd :: ProofCmd)              -> cmd
  ]

