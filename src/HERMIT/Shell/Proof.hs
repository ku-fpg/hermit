{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}

module HERMIT.Shell.Proof
    ( externals
    , UserProofTechnique
    , userProofTechnique
    , reEnterProofIO
    ) where

import Control.Arrow hiding (loop, (<+>))
import Control.Monad ((>=>), forM, forM_, liftM, unless)
import Control.Monad.Error.Class (MonadError(..))
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.State (MonadState(get), modify, gets)
import Control.Monad.Trans.Class (lift)

import Data.Char (isSpace)
import Data.Dynamic
import Data.List (delete)
import qualified Data.Map as M
import Data.Monoid
import Data.String (fromString)

import HERMIT.Context
import HERMIT.Core
import HERMIT.External
import HERMIT.GHC hiding (settings, (<>), text, sep, (<+>), ($+$), nest)
import HERMIT.Kernel
import HERMIT.Kure
import HERMIT.Lemma
import HERMIT.Monad
import HERMIT.Parser
import HERMIT.Syntax
import HERMIT.Utilities

import HERMIT.Dictionary.Induction
import HERMIT.Dictionary.Reasoning hiding (externals)

import HERMIT.PrettyPrinter.Common

import HERMIT.Shell.Completion
import HERMIT.Shell.Interpreter
import HERMIT.Shell.KernelEffect
import HERMIT.Shell.ScriptToRewrite
import HERMIT.Shell.ShellEffect
import HERMIT.Shell.Types

import System.Console.Haskeline hiding (catch, display)
import System.IO

--------------------------------------------------------------------------------------------------------

-- | Externals that get us into the prover shell.
externals :: [External]
externals = map (.+ Proof)
    [ external "prove-lemma" (CLSModify . interactiveProofIO)
        [ "Proof a lemma interactively." ]
    ]

-- | Externals that are added to the dictionary only when in interactive proof mode.
proof_externals :: [External]
proof_externals = map (.+ Proof)
    [ external "induction" (PCInduction . cmpString2Var :: String -> ProofShellCommand)
        [ "Perform induction on given universally quantified variable."
        , "Each constructor case will generate a new lemma to be proven."
        ]
    , external "prove-consequent" PCConsequent
        [ "Prove the consequent of an implication by assuming the antecedent." ]
    , external "prove-antecedent" PCAntecedent
        [ "Introduce a proven lemma corresponding to the consequent by proving the antecedent." ]
    , external "prove-conjuction" PCConjunction
        [ "Prove a conjuction by proving both sides of it." ]
    , external "split-assumed" PCSplitAssumed
        [ "Split an assumed lemma which is a conjuction/disjunction." ]
    , external "dump" (\pp fp r w -> promoteT (liftPrettyH (pOptions pp) (ppQuantifiedT pp)) >>> dumpT fp pp r w :: TransformH QC ())
        [ "dump <filename> <renderer> <width>" ]
    , external "end-proof" PCEnd
        [ "check for alpha-equality, marking the lemma as proven" ]
    , external "end-case" PCEnd
        [ "check for alpha-equality, marking the proof case as proven" ]
    ]

--------------------------------------------------------------------------------------------------------

printLemma :: (MonadCatch m, MonadError CLException m, MonadIO m, MonadState CommandLineState m)
           => PathStack -> (LemmaName,Lemma) -> m ()
printLemma p (nm,lem) = do -- TODO
    pp <- gets cl_pretty
    doc <- queryInFocus (return lem >>> liftPrettyH (pOptions pp) (ppLemmaT (pathStack2Path p) pp nm) :: TransformH Core DocH) Never
    st <- get
    liftIO $ cl_render st stdout (cl_pretty_opts st) (Right doc)

--------------------------------------------------------------------------------------------------------

-- | Top level entry point! Assumption is that proof stack is empty if this is called.
interactiveProofIO :: LemmaName -> CommandLineState -> IO (Either CLException CommandLineState)
interactiveProofIO nm s = do
    (r,st) <- runCLT s $ do
                l <- queryInFocus (getLemmaByNameT nm :: TransformH Core Lemma) (Always $ "prove-lemma " ++ quoteShow nm)
                pushProofStack $ Unproven nm l [] mempty False
                interactiveProof
    -- Proof stack in st will always be empty
    return $ fmap (const st) r

-- | Used by the version commands to resume a proof after 'goto'.
reEnterProofIO :: CommandLineState -> IO (Either CLException CommandLineState)
reEnterProofIO s = do
    (r,st) <- runCLT s interactiveProof
    return $ fmap (const st) r

-- | If the proof stack is empty, this is a no-op.
interactiveProof :: forall m. (MonadCatch m, MonadException m, CLMonad m) => m ()
interactiveProof = do
    let -- Main proof input loop
        loop :: InputT m ()
        loop = do
            el <- lift $ tryM () announceProven >> attemptM currentLemma
            case el of
                Left _ -> return () -- no lemma is currently being proven, so exit
                Right (nm,l,ls,p) -> do
                    mExpr <- lift popScriptLine
                    case mExpr of
                        Nothing -> do
                            lift $ do
                                unless (null ls) $ do
                                    cl_putStrLn "Assumed lemmas:"
                                    mapM_ (printLemma mempty)
                                          [ (fromString (show i) <> ": " <> n, lem)
                                          | (i::Int,(n,lem)) <- zip [0..] ls ]
                                printLemma p (nm,l)
                            mLine <- getInputLine $ "proof> "
                            case mLine of
                                Nothing          -> fail "proof aborted (input: Nothing)"
                                Just ('-':'-':_) -> loop
                                Just line        -> do unless (all isSpace line) $
                                                            lift (evalProofScript line `catchM` cl_putStrLn)
                                                       loop
                        Just e -> lift (runExprH e `catchM` (\ msg -> setRunningScript Nothing >> cl_putStrLn msg)) >> loop

        settings = setComplete (completeWordWithPrev Nothing " ()" shellComplete) defaultSettings

    withProofExternals $ runInputT settings loop

withProofExternals :: (MonadError CLException m, MonadState CommandLineState m) => m a -> m a
withProofExternals comp = do
    st <- get
    let es = cl_externals st
        -- commands with same same in proof_externals will override those in normal externals
        newEs = proof_externals ++ filter ((`notElem` (map externName proof_externals)) . externName) es
        reset s = s { cl_externals = es }
    modify $ \ s -> s { cl_externals = newEs }
    r <- comp `catchError` (\case CLContinue s -> continue (reset s)
                                  other        -> modify reset >> throwError other)
    modify reset
    return r

evalProofScript :: (MonadCatch m, MonadException m, CLMonad m) => String -> m ()
evalProofScript = parseScriptCLT >=> mapM_ runExprH

runExprH :: (MonadCatch m, MonadException m, CLMonad m) => ExprH -> m ()
runExprH expr = prefixFailMsg ("Error in expression: " ++ unparseExprH expr ++ "\n")
              $ interpExprH interpProof expr >>= performProofShellCommand expr

transformQ :: Quantified -> [NamedLemma] -> TransformH QC a -> TransformH Core a
transformQ q ls t = contextonlyT $ \ c -> withLemmas (M.fromList ls) (applyT (extractT t) c q)

rewriteQ :: Quantified -> [NamedLemma] -> RewriteH QC -> TransformH Core Quantified
rewriteQ q ls rr = contextonlyT $ \ c -> withLemmas (M.fromList ls) (applyT (extractR rr) c q)

-- | Verify that the lemma has been proven. Throws an exception if it has not.
endProof :: (MonadCatch m, CLMonad m) => ExprH -> m ()
endProof expr = do
    Unproven nm (Lemma q _ _) ls _ temp : _ <- getProofStack
    let msg = "The two sides of " ++ quoteShow nm ++ " are not alpha-equivalent."
        t = promoteT $ verifyQuantifiedT >> unless temp (markLemmaProvedT nm)
    queryInFocus (transformQ q ls (setFailMsg msg t)) (Always $ unparseExprH expr ++ " -- proven " ++ quoteShow nm)
    _ <- popProofStack
    cl_putStrLn $ "Successfully proven: " ++ show nm

-- Note [Query]
-- We want to do our proof in the current context of the shell, whatever that is,
-- so we run them using queryInFocus below. This has the benefit that proof commands
-- can generate additional lemmas, and add to the version history.
performProofShellCommand :: (MonadCatch m, MonadException m, CLMonad m)
                         => ExprH -> ProofShellCommand -> m ()
performProofShellCommand expr = go
    where str = unparseExprH expr
          go (PCRewrite rr) = do
                -- careful to only modify the lemma in the resulting AST
                Unproven nm (Lemma q p u) ls pth t : todos <- getProofStack
                q' <- queryInFocus (rewriteQ q ls $ pathR (pathStack2Path pth) rr >>> (promoteT lintQuantifiedT >> idR)) (Always str)
                let todo = Unproven nm (Lemma q' p u) ls pth t
                modify $ \ st -> st { cl_proofstack = M.insert (cl_cursor st) (todo:todos) (cl_proofstack st) }
          go (PCTransform t) = do
                (_, Lemma q _ _, ls, p) <- currentLemma
                cl_putStrLn =<< queryInFocus (transformQ q ls $ pathT (pathStack2Path p) t) (Changed str)
          go (PCUnit t) = do
                (_, Lemma q _ _, ls, p) <- currentLemma
                queryInFocus (transformQ q ls $ pathT (pathStack2Path p) t) (Changed str)
          go (PCInduction idPred) = performInduction (Always str) idPred
          go PCConsequent         = proveConsequent str
          go PCAntecedent         = proveAntecedent str
          go PCConjunction        = proveConjuction str
          go (PCSplitAssumed i)   = splitAssumed i str
          go (PCShell effect)     = performShellEffect effect
          go (PCKernel effect)    = performKernelEffect expr effect
          go (PCScript effect)    = performScriptEffect runExprH effect
          go (PCQuery query)      = performQuery query expr
          go (PCUser prf)         = do
                let UserProofTechnique t = prf -- may add more constructors later
                -- note: we assume that if 't' completes without failing,
                -- the lemma is proved, we don't actually check
                Unproven nm (Lemma q _ _) ls _ temp : _ <- getProofStack
                queryInFocus (transformQ q ls t >> unless temp (markLemmaProvedT nm)) (Changed str)
                _ <- popProofStack
                cl_putStrLn $ "Successfully proven: " ++ show nm
          go PCEnd                = endProof expr
          go (PCPath tr) = do
                Unproven nm (Lemma q p u) ls (base,pth) t : todos <- getProofStack
                pth' <- queryInFocus (transformQ q ls $ localPathT pth tr) (Always str)
                -- TODO: test if valid path
                let todo = Unproven nm (Lemma q p u) ls (base, pth <> pth') t
                modify $ \ st -> st { cl_proofstack = M.insert (cl_cursor st) (todo:todos) (cl_proofstack st) }
          go (PCUnsupported s)    = cl_putStrLn (s ++ " command unsupported in proof mode.")

proveConsequent :: (MonadCatch m, CLMonad m) => String -> m ()
proveConsequent expr = do
    Unproven nm (Lemma (Quantified bs cl) p u) ls _ t : _ <- getProofStack
    (q,ls') <- case cl of
                Impl ante (Quantified cBs ccl) ->
                    let n = nm <> "-antecedent"
                        l = Lemma ante True False
                    in return (Quantified (bs++cBs) ccl, (n,l):ls)
                _ -> fail "not an implication."
    let nm' = nm <> "-consequent"
    (k,ast) <- gets (cl_kernel &&& cl_cursor)
    addAST =<< tellK k expr ast
    _ <- popProofStack
    pushProofStack $ Proven nm t -- proving the consequent proves the lemma
    pushProofStack $ Unproven nm' (Lemma q p u) ls' mempty True

proveAntecedent :: (MonadCatch m, CLMonad m) => String -> m ()
proveAntecedent expr = do
    Unproven nm (Lemma (Quantified bs cl) p u) ls _ _ : _ <- getProofStack
    case cl of
        Impl (Quantified aBs acl) (Quantified cBs ccl) -> do
            let cnm = nm <> "-consequent"
                cq = Quantified (bs++cBs) ccl
                anm = nm <> "-antecedent"
                alem = Lemma (Quantified (bs++aBs) acl) False u
            (k,ast) <- gets (cl_kernel &&& cl_cursor)
            addAST =<< tellK k expr ast
            _ <- popProofStack
            pushProofStack $ IntroLemma cnm cq p -- proving the antecedent introduces the consequent as a lemma
            pushProofStack $ Unproven anm alem ls mempty True
        _ -> fail "not an implication."

proveConjuction :: (MonadCatch m, CLMonad m) => String -> m ()
proveConjuction expr = do
    Unproven nm (Lemma (Quantified bs cl) p u) ls _ t : _ <- getProofStack
    case cl of
        Conj (Quantified lbs lcl) (Quantified rbs rcl) -> do
            (k,ast) <- gets (cl_kernel &&& cl_cursor)
            addAST =<< tellK k expr ast
            _ <- popProofStack
            pushProofStack $ Proven nm t
            pushProofStack $ Unproven (nm <> "-r") (Lemma (Quantified (bs++rbs) rcl) p u) ls mempty True
            pushProofStack $ Unproven (nm <> "-l") (Lemma (Quantified (bs++lbs) lcl) p u) ls mempty True
        _ -> fail "not a conjuction."

splitAssumed :: (MonadCatch m, CLMonad m) => Int -> String -> m ()
splitAssumed i expr = do
    Unproven nm lem ls _ t : _ <- getProofStack
    (b, (n, Lemma q p u):a) <- getIth i ls
    qs <- splitQuantified q
    let nls = [ (n <> fromString (show j), Lemma q' p u) | (j::Int,q') <- zip [0..] qs ]
    (k,ast) <- gets (cl_kernel &&& cl_cursor)
    addAST =<< tellK k expr ast
    _ <- popProofStack
    pushProofStack $ Unproven nm lem (b ++ nls ++ a) mempty t

getIth :: MonadCatch m => Int -> [a] -> m ([a],[a])
getIth _ [] = fail "getIth: out of range"
getIth n (x:xs) = go n x xs []
    where go 0 y ys zs = return (reverse zs, y:ys)
          go _ _ [] _  = fail "getIth: out of range"
          go i z (y:ys) zs = go (i-1) y ys (z:zs)

-- | Always returns non-empty list, or fails.
splitQuantified :: MonadCatch m => Quantified -> m [Quantified]
splitQuantified (Quantified bs cl) = do
    case cl of
        Conj (Quantified lbs lcl) (Quantified rbs rcl) ->
            return [Quantified (bs++lbs) lcl, Quantified (bs++rbs) rcl]
        Disj (Quantified lbs lcl) (Quantified rbs rcl) ->
            return [Quantified (bs++lbs) lcl, Quantified (bs++rbs) rcl]
        Impl (Quantified lbs lcl) (Quantified rbs rcl) ->
            return [Quantified (bs++lbs) lcl, Quantified (bs++rbs) rcl]
        _ -> fail "equalities cannot be split!"

performInduction :: (MonadCatch m, MonadException m, CLMonad m)
                 => CommitMsg -> (Id -> Bool) -> m ()
performInduction cm idPred = do
    (nm, Lemma q@(Quantified bs (Equiv lhs rhs)) _ _, ls, _) <- currentLemma
    i <- setFailMsg "specified identifier is not universally quantified in this equality lemma." $
         soleElement (filter idPred bs)

    -- Why do a query? We want to do our proof in the current context of the shell, whatever that is.
    cases <- queryInFocus (inductionCaseSplit bs i lhs rhs :: TransformH Core [(Maybe DataCon, [Var], CoreExpr, CoreExpr)])
                          cm

    -- replace the current lemma with the three subcases
    -- proving them will prove this case automatically
    Unproven _ _ _ _ t <- popProofStack
    pushProofStack $ Proven nm t
    forM_ (reverse cases) $ \ (mdc,vs,lhsE,rhsE) -> do

        let vs_matching_i_type = filter (typeAlphaEq (varType i) . varType) vs
            caseName = maybe "undefined" unqualifiedName mdc

        -- Generate list of specialized induction hypotheses for the recursive cases.
        qs <- forM vs_matching_i_type $ \ i' -> do
                liftM discardUniVars $ instQuantified (==i) (Var i') q
                -- TODO rethink the discardUniVars

        let nms = [ fromString ("ind-hyp-" ++ show n) | n :: Int <- [0..] ]
            hypLemmas = zip nms $ zipWith3 Lemma qs (repeat True) (repeat False)
            lemmaName = fromString $ show nm ++ "-induction-on-" ++ unqualifiedName i ++ "-case-" ++ caseName
            caseLemma = Lemma (mkQuantified (delete i bs ++ vs) lhsE rhsE) False False

        pushProofStack $ Unproven lemmaName caseLemma (hypLemmas ++ ls) mempty True

data ProofShellCommand
    = PCRewrite (RewriteH QC)
    | PCTransform (TransformH QC String)
    | PCUnit (TransformH QC ())
    | PCInduction (Id -> Bool)
    | PCConsequent
    | PCAntecedent
    | PCConjunction
    | PCSplitAssumed Int
    | PCShell ShellEffect
    | PCKernel KernelEffect
    | PCScript ScriptEffect
    | PCQuery QueryFun
    | PCUser UserProofTechnique
    | PCEnd
    | PCPath (TransformH QC LocalPathH)
    | PCUnsupported String
    deriving Typeable

-- keep abstract to avoid breaking things if we modify this later
newtype UserProofTechnique = UserProofTechnique (TransformH QC ())
    deriving Typeable

userProofTechnique :: TransformH QC () -> UserProofTechnique
userProofTechnique = UserProofTechnique

instance Extern ProofShellCommand where
    type Box ProofShellCommand = ProofShellCommand
    box i = i
    unbox i = i

instance Extern UserProofTechnique where
    type Box UserProofTechnique = UserProofTechnique
    box i = i
    unbox i = i

interpProof :: Monad m => [Interp m ProofShellCommand]
interpProof =
  [ interp $ \ (RewriteCoreBox rr)            -> PCRewrite $ core2qcR rr
  , interp $ \ (RewriteCoreTCBox rr)          -> PCRewrite $ core2qcR $ extractR rr
  , interp $ \ (BiRewriteCoreBox br)          -> PCRewrite $ core2qcR $ forwardT br <+ backwardT br
  , interp $ \ (effect :: ShellEffect)        -> PCShell effect
  , interp $ \ (effect :: KernelEffect)       -> PCKernel effect
  , interp $ \ (effect :: ScriptEffect)       -> PCScript effect
  , interp $ \ (StringBox str)                -> PCQuery (message str)
  , interp $ \ (query :: QueryFun)            -> PCQuery query
  , interp $ \ (RewriteQCBox r)               -> PCRewrite r
  , interp $ \ (TransformQCStringBox t)       -> PCTransform t
  , interp $ \ (TransformQCUnitBox t)         -> PCUnit t
  , interp $ \ (t :: UserProofTechnique)      -> PCUser t
  , interp $ \ (cmd :: ProofShellCommand)     -> cmd
  , interp $ \ (CrumbBox cr)                  -> PCPath (return $ mempty @@ cr)
  , interp $ \ (PathBox p)                    -> PCPath (return p)
  , interp $ \ (TransformCorePathBox tt)      -> PCPath (promoteT (extractT tt :: TransformH CoreExpr LocalPathH))
  , interp $ \ (TransformCoreTCPathBox tt)    -> PCPath (promoteT (extractT tt :: TransformH CoreExpr LocalPathH))
  , interp $ \ (TransformCoreDocHBox t)       -> PCQuery (QueryDocH t)
  , interp $ \ (TransformCoreTCDocHBox t)     -> PCQuery (QueryDocH t)
  , interp $ \ (PrettyHCoreBox t)             -> PCQuery (QueryPrettyH t)
  , interp $ \ (PrettyHCoreTCBox t)           -> PCQuery (QueryPrettyH t)
  , interp $ \ (TransformCoreStringBox tt)    -> PCQuery (QueryString tt)
  , interp $ \ (TransformCoreTCStringBox tt)  -> PCQuery (QueryString tt)
  , interp $ \ (TransformCoreCheckBox tt)     -> PCQuery (CorrectnessCriteria tt)
  , interp $ \ (TransformCoreTCCheckBox tt)   -> PCQuery (CorrectnessCriteria tt)
  -- , interp $ \ (_effect :: KernelEffect)      -> PCUnsupported "KernelEffect"
  ]

