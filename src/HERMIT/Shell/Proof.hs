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
import Data.String (fromString)

import HERMIT.Core
import HERMIT.External
import HERMIT.GHC hiding (settings, (<>), text, sep, (<+>), ($+$), nest)
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
    , external "dump" (\pp fp r w -> promoteT (liftPrettyH (pOptions pp) (ppQuantifiedT pp)) >>> dumpT fp pp r w :: TransformH QC ())
        [ "dump <filename> <renderer> <width>" ]
    , external "end-proof" PCEnd
        [ "check for alpha-equality, marking the lemma as proven" ]
    , external "end-case" PCEnd
        [ "check for alpha-equality, marking the proof case as proven" ]
    ]

--------------------------------------------------------------------------------------------------------

printLemma :: (MonadCatch m, MonadError CLException m, MonadIO m, MonadState CommandLineState m)
           => (LemmaName,Lemma) -> m ()
printLemma (nm,lem) = do
    pp <- gets cl_pretty
    doc <- queryInFocus (return lem >>> liftPrettyH (pOptions pp) (ppLemmaT pp nm) :: TransformH Core DocH) Nothing
    st <- get
    liftIO $ cl_render st stdout (cl_pretty_opts st) (Right doc)

--------------------------------------------------------------------------------------------------------

-- | Top level entry point! Assumption is that proof stack is empty if this is called.
interactiveProofIO :: LemmaName -> CommandLineState -> IO (Either CLException CommandLineState)
interactiveProofIO nm s = do
    (r,st) <- runCLT s $ do
                l <- queryInFocus (getLemmaByNameT nm :: TransformH Core Lemma) (Just $ "prove-lemma " ++ quoteShow nm)
                pushProofStack $ Unproven nm l [] False
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
                Right (nm,l,_) -> do
                    mExpr <- lift popScriptLine
                    case mExpr of
                        Nothing -> do
                            lift $ printLemma (nm,l)
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
    Unproven nm (Lemma q _ _) ls temp : _ <- getProofStack
    let msg = "The two sides of " ++ quoteShow nm ++ " are not alpha-equivalent."
        t = promoteT $ verifyQuantifiedT >> unless temp (markLemmaProvedT nm)
    queryInFocus (transformQ q ls (setFailMsg msg t)) (Just $ unparseExprH expr ++ " -- proven " ++ quoteShow nm)
    _ <- popProofStack
    cl_putStrLn $ "Successfully proven: " ++ show nm

-- Note [Query]
-- We want to do our proof in the current context of the shell, whatever that is,
-- so we run them using queryInFocus below. This has the benefit that proof commands
-- can generate additional lemmas, and add to the version history.
performProofShellCommand :: (MonadCatch m, MonadException m, CLMonad m)
                         => ExprH -> ProofShellCommand -> m ()
performProofShellCommand expr = go
    where expr' = Just $ unparseExprH expr
          go (PCRewrite rr) = do
                -- careful to only modify the lemma in the resulting AST
                Unproven nm (Lemma q p u) ls t : todos <- getProofStack
                q' <- queryInFocus (rewriteQ q ls $ rr >>> (promoteT lintQuantifiedT >> idR)) expr'
                let todo = Unproven nm (Lemma q' p u) ls t
                modify $ \ st -> st { cl_proofstack = M.insert (cl_cursor st) (todo:todos) (cl_proofstack st) }
          go (PCTransform t) = do
                (_, Lemma q _ _, ls) <- currentLemma
                cl_putStrLn =<< queryInFocus (transformQ q ls t) expr'
          go (PCUnit t) = do
                (_, Lemma q _ _, ls) <- currentLemma
                queryInFocus (transformQ q ls t) expr'
          go (PCInduction idPred) = performInduction expr' idPred
          go (PCShell effect)     = performShellEffect effect
          go (PCScript effect)    = do
                -- lemVar <- liftIO $ newMVar lem -- couldn't resist that name
                -- let lemHack e = liftIO (takeMVar lemVar) >>= flip runExprH e >>= liftIO . putMVar lemVar
                performScriptEffect runExprH effect
                -- liftIO $ takeMVar lemVar
          go (PCQuery query)      = performQuery query expr
          go (PCUser prf)         = do
                let UserProofTechnique t = prf -- may add more constructors later
                -- note: we assume that if 't' completes without failing,
                -- the lemma is proved, we don't actually check
                Unproven nm (Lemma q _ _) ls temp : _ <- getProofStack
                queryInFocus (transformQ q ls t >> unless temp (markLemmaProvedT nm)) expr'
                _ <- popProofStack
                cl_putStrLn $ "Successfully proven: " ++ show nm
          go PCEnd                = endProof expr
          go (PCUnsupported s)    = cl_putStrLn (s ++ " command unsupported in proof mode.")

performInduction :: (MonadCatch m, MonadException m, CLMonad m)
                 => Maybe String -> (Id -> Bool) -> m ()
performInduction expr idPred = do
    (nm, Lemma q@(Quantified bs (Equiv lhs rhs)) _ _, ls) <- currentLemma
    i <- setFailMsg "specified identifier is not universally quantified in this equality lemma." $
         soleElement (filter idPred bs)

    -- Why do a query? We want to do our proof in the current context of the shell, whatever that is.
    cases <- queryInFocus (inductionCaseSplit bs i lhs rhs :: TransformH Core [(Maybe DataCon, [Var], CoreExpr, CoreExpr)])
                          expr

    -- replace the current lemma with the three subcases
    -- proving them will prove this case automatically
    Unproven _ _ _ t <- popProofStack
    pushProofStack $ Proven nm t
    forM_ (reverse cases) $ \ (mdc,vs,lhsE,rhsE) -> do

        let vs_matching_i_type = filter (typeAlphaEq (varType i) . varType) vs
            caseName = maybe "undefined" unqualifiedName mdc

        -- Generate list of specialized induction hypotheses for the recursive cases.
        qs <- forM vs_matching_i_type $ \ i' -> do
                liftM discardUniVars $ instantiateQuantifiedVar (==i) (Var i') [] q
                -- TODO rethink the discardUniVars

        let nms = [ fromString ("ind-hyp-" ++ show n) | n :: Int <- [0..] ]
            hypLemmas = zip nms $ zipWith3 Lemma qs (repeat True) (repeat False)
            lemmaName = fromString $ show nm ++ "-induction-on-" ++ unqualifiedName i ++ "-case-" ++ caseName
            caseLemma = Lemma (mkQuantified (delete i bs ++ vs) lhsE rhsE) False False

        pushProofStack $ Unproven lemmaName caseLemma (hypLemmas ++ ls) True

data ProofShellCommand
    = PCRewrite (RewriteH QC)
    | PCTransform (TransformH QC String)
    | PCUnit (TransformH QC ())
    | PCInduction (Id -> Bool)
    | PCShell ShellEffect
    | PCScript ScriptEffect
    | PCQuery QueryFun
    | PCUser UserProofTechnique
    | PCEnd
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
  [ interp $ \ (RewriteCoreBox rr)            -> PCRewrite $ promoteR $ bothR $ core2qcR rr
  , interp $ \ (RewriteCoreTCBox rr)          -> PCRewrite $ promoteR $ bothR $ core2qcR $ extractR rr
  , interp $ \ (BiRewriteCoreBox br)          -> PCRewrite $ promoteR $ bothR $ core2qcR $ forwardT br <+ backwardT br
  , interp $ \ (effect :: ShellEffect)        -> PCShell effect
  , interp $ \ (effect :: ScriptEffect)       -> PCScript effect
  , interp $ \ (StringBox str)                -> PCQuery (message str)
  , interp $ \ (query :: QueryFun)            -> PCQuery query
  , interp $ \ (RewriteQCBox r)               -> PCRewrite r
  , interp $ \ (TransformQCStringBox t)       -> PCTransform t
  , interp $ \ (TransformQCUnitBox t)         -> PCUnit t
  , interp $ \ (t :: UserProofTechnique)      -> PCUser t
  , interp $ \ (cmd :: ProofShellCommand)     -> cmd
  , interp $ \ (CrumbBox _cr)                 -> PCUnsupported "CrumbBox"
  , interp $ \ (PathBox _p)                   -> PCUnsupported "PathBox"
  , interp $ \ (TransformCorePathBox _tt)     -> PCUnsupported "TransformCorePathBox"
  , interp $ \ (TransformCoreTCPathBox _tt)   -> PCUnsupported "TransformCoreTCPathBox"
  , interp $ \ (TransformCoreDocHBox t)       -> PCQuery (QueryDocH t)
  , interp $ \ (TransformCoreTCDocHBox t)     -> PCQuery (QueryDocH t)
  , interp $ \ (PrettyHCoreBox t)             -> PCQuery (QueryPrettyH t)
  , interp $ \ (PrettyHCoreTCBox t)           -> PCQuery (QueryPrettyH t)
  , interp $ \ (TransformCoreStringBox tt)    -> PCQuery (QueryString tt)
  , interp $ \ (TransformCoreTCStringBox tt)  -> PCQuery (QueryString tt)
  , interp $ \ (TransformCoreCheckBox tt)     -> PCQuery (CorrectnessCriteria tt)
  , interp $ \ (TransformCoreTCCheckBox tt)   -> PCQuery (CorrectnessCriteria tt)
  , interp $ \ (_effect :: KernelEffect)      -> PCUnsupported "KernelEffect"
  ]

