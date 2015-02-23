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
    ) where

import Control.Arrow hiding (loop, (<+>))
import Control.Concurrent
import Control.Monad ((>=>), foldM, forM, forM_, liftM, unless, when)
import Control.Monad.Error.Class (MonadError(catchError))
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.State (MonadState(get, put), modify, gets)
import Control.Monad.Trans.Class (lift)

import Data.Char (isSpace)
import Data.Dynamic
import Data.List (delete, intercalate)
import Data.String (fromString)

import HERMIT.Core
import HERMIT.Equality
import HERMIT.External
import HERMIT.GHC hiding (settings, (<>), text, sep, (<+>), ($+$), nest)
import HERMIT.Kernel
import HERMIT.Kure
import HERMIT.Monad
import HERMIT.Parser
import HERMIT.Syntax
import HERMIT.Utilities

import HERMIT.Dictionary.GHC hiding (externals)
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
        , "Each constructor case will generate a new equality to be proven."
        ]
    , external "dump" (\pp fp r w -> liftPrettyH (pOptions pp) (ppEqualityT pp) >>> dumpT fp pp r w)
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

type NamedLemma = (LemmaName, Lemma)

interactiveProofIO :: LemmaName -> CommandLineState -> IO (Either CLException CommandLineState)
interactiveProofIO nm s = do
    (r,s') <- runCLT s $ do
                l <- queryInFocus (getLemmaByNameT nm :: TransformH Core Lemma) (Just $ "prove-lemma " ++ quoteShow nm)
                interactiveProof True (nm,l)
    return $ fmap (const s') r

interactiveProof :: forall m. (MonadCatch m, MonadException m, CLMonad m) => Bool -> NamedLemma -> m ()
interactiveProof topLevel lem@(nm,_) = do
    let ws_complete = " ()"

        -- Main proof input loop
        loop :: NamedLemma -> InputT m ()
        loop l = do
            mExpr <- lift popScriptLine
            case mExpr of
                Nothing -> do
                    lift $ printLemma l
                    mLine <- getInputLine $ "proof> "
                    case mLine of
                        Nothing          -> fail "proof aborted (input: Nothing)"
                        Just ('-':'-':_) -> loop l
                        Just line        -> if all isSpace line
                                            then loop l
                                            else lift (evalProofScript l line
                                                        `catchM` (\msg -> cl_putStrLn msg >> return l)) >>= loop
                Just e -> lift (runExprH l e
                                    `catchM` (\msg -> setRunningScript Nothing >> cl_putStrLn msg >> return l)) >>= loop

        settings = setComplete (completeWordWithPrev Nothing ws_complete shellComplete) defaultSettings

    origSt <- get

    catchError (withProofExternals topLevel $ runInputT settings (loop lem))
               (\case
                    CLAbort        -> put origSt -- abandon proof attempt
                    CLContinue st' -> do
                        cl_putStrLn $ "Successfully proven: " ++ quoteShow nm
                        put st'
                        when topLevel $
                            queryInFocus (modifyLemmaT nm id idR (const True) id :: TransformH Core ())
                                         (Just $ "-- proven " ++ quoteShow nm) -- comment in script

                    CLError msg    -> fail $ "Prover error: " ++ msg
                    _              -> fail "unsupported exception in interactive prover")

withProofExternals :: MonadState CommandLineState m => Bool -> m a -> m a
withProofExternals False comp = comp
withProofExternals True  comp = do
    st <- get
    let es = cl_externals st
        -- commands with same same in proof_externals will override those in normal externals
        newEs = proof_externals ++ filter ((`notElem` (map externName proof_externals)) . externName) es
    modify $ \ s -> s { cl_externals = newEs }
    r <- comp
    modify $ \ s -> s { cl_externals = es }
    return r

evalProofScript :: (MonadCatch m, MonadException m, CLMonad m) => NamedLemma -> String -> m NamedLemma
evalProofScript lem = parseScriptCLT >=> foldM runExprH lem

runExprH :: (MonadCatch m, MonadException m, CLMonad m) => NamedLemma -> ExprH -> m NamedLemma
runExprH lem expr = prefixFailMsg ("Error in expression: " ++ unparseExprH expr ++ "\n")
                  $ interpExprH interpProof expr >>= performProofShellCommand expr lem

-- | Verify that the lemma has been proven. Throws an exception if it has not.
endProof :: (MonadCatch m, MonadError CLException m, MonadIO m, MonadState CommandLineState m) => ExprH -> NamedLemma -> m ()
endProof expr (nm, Lemma eq _ _) = do
    b <- queryInFocus (return eq >>> testM verifyEqualityT :: TransformH Core Bool) Nothing
    if b
    then do st <- get
            addAST =<< tellK (cl_kernel st) (unparseExprH expr) (cl_cursor st)
            get >>= continue
    else fail $ "The two sides of " ++ quoteShow nm ++ " are not alpha-equivalent."

-- Note [Query]
-- We want to do our proof in the current context of the shell, whatever that is,
-- so we run them using queryInFocus below. This has the benefit that proof commands
-- can generate additional lemmas, and add to the version history.
performProofShellCommand :: (MonadCatch m, MonadException m, CLMonad m) => ExprH -> NamedLemma -> ProofShellCommand -> m NamedLemma
performProofShellCommand expr lem@(nm, Lemma eq p u) = go
    where expr' = Just $ unparseExprH expr
          go (PCRewrite rr) = do
                eq' <- queryInFocus (return eq >>> rr >>> (bothT lintExprT >> idR) :: TransformH Core Equality) expr'
                return (nm, Lemma eq' p u)
          go (PCTransform t) = do
                cl_putStrLn =<< queryInFocus (return eq >>> t :: TransformH Core String) expr'
                return lem
          go (PCUnit t) = do
                queryInFocus (return eq >>> t :: TransformH Core ()) expr'
                return lem
          go (PCInduction idPred) = performInduction expr' lem idPred
          go (PCShell effect)     = performShellEffect effect >> return lem
          go (PCScript effect)    = do
                lemVar <- liftIO $ newMVar lem -- couldn't resist that name
                let lemHack e = liftIO (takeMVar lemVar) >>= flip runExprH e >>= liftIO . putMVar lemVar
                performScriptEffect lemHack effect
                liftIO $ takeMVar lemVar
          go (PCQuery query)      = performQuery query expr >> return lem
          go (PCUser prf)         = do
                let UserProofTechnique t = prf -- may add more constructors later
                queryInFocus (return eq >>> t :: TransformH Core ()) expr'
                get >>= continue -- note: we assume that if 't' completes without failing,
                                 -- the lemma is proved, we don't actually check
                return lem       -- never reached, but makes types happy
          go PCEnd                = endProof expr lem >> return lem
          go (PCUnsupported s)    = cl_putStrLn (s ++ " command unsupported in proof mode.") >> return lem

performInduction :: (MonadCatch m, MonadException m, CLMonad m)
                 => Maybe String -> NamedLemma -> (Id -> Bool) -> m NamedLemma
performInduction expr lem@(nm, Lemma eq@(Equality bs lhs rhs) _ _) idPred = do
    i <- setFailMsg "specified identifier is not universally quantified in this equality lemma." $
         soleElement (filter idPred bs)

    -- Why do a query? We want to do our proof in the current context of the shell, whatever that is.
    cases <- queryInFocus (inductionCaseSplit bs i lhs rhs :: TransformH Core [(Maybe DataCon, [Var], CoreExpr, CoreExpr)])
                          expr

    forM_ cases $ \ (mdc,vs,lhsE,rhsE) -> do

        let vs_matching_i_type = filter (typeAlphaEq (varType i) . varType) vs
            -- TODO rethink the remake.discardUniVars
            remake (Equality bndrs l r) = mkEquality bndrs l r
            caseName = maybe "undefined" unqualifiedName mdc

        (k,ast) <- gets (cl_kernel &&& cl_cursor)
        addAST =<< tellK k ("-- case: " ++ caseName) ast

        -- Generate list of specialized induction hypotheses for the recursive cases.
        eqs <- forM vs_matching_i_type $ \ i' ->
                    liftM (remake.discardUniVars) $ instantiateEqualityVar (==i) (Var i') [] eq

        let nms = [ fromString ("ind-hyp-" ++ show n) | n :: Int <- [0..] ]
            hypLemmas = zip nms $ zipWith3 Lemma eqs (repeat True) (repeat False)
            lemmaName = fromString $ show nm ++ "-induction-on-" ++ unqualifiedName i ++ "-case-" ++ caseName
            caseLemma = Lemma (Equality (delete i bs ++ vs) lhsE rhsE) False False

        withLemmas hypLemmas $ interactiveProof False (lemmaName,caseLemma) -- recursion!

    get >>= continue
    return lem -- this is never reached, but the type says we need it.

withLemmas :: (MonadCatch m, CLMonad m) => [NamedLemma] -> m a -> m a
withLemmas []   comp = comp
withLemmas lems comp = do
    ifM isRunningScript (return ()) $ forM_ lems printLemma

    let lemmaNames = intercalate ", " $ map (quoteShow . fst) lems

    ls <- queryInFocus (getLemmasT :: TransformH Core Lemmas) Nothing
    queryInFocus (constT (forM_ lems $ \ (nm,l) -> insertLemma nm l) :: TransformH Core ())
                 (Just $ "-- adding lemmas: " ++ lemmaNames)
    r <- comp
    queryInFocus (constT (putLemmas ls) :: TransformH Core ())
                 (Just $ "-- removing lemmas: " ++ lemmaNames)
    return r

data ProofShellCommand
    = PCRewrite (RewriteH Equality)
    | PCTransform (TransformH Equality String)
    | PCUnit (TransformH Equality ())
    | PCInduction (Id -> Bool)
    | PCShell ShellEffect
    | PCScript ScriptEffect
    | PCQuery QueryFun
    | PCUser UserProofTechnique
    | PCEnd
    | PCUnsupported String
    deriving Typeable

-- keep abstract to avoid breaking things if we modify this later
newtype UserProofTechnique = UserProofTechnique (TransformH Equality ())

userProofTechnique :: TransformH Equality () -> UserProofTechnique
userProofTechnique = UserProofTechnique

instance Extern ProofShellCommand where
    type Box ProofShellCommand = ProofShellCommand
    box i = i
    unbox i = i

data UserProofTechniqueBox = UserProofTechniqueBox UserProofTechnique deriving Typeable

instance Extern UserProofTechnique where
    type Box UserProofTechnique = UserProofTechniqueBox
    box = UserProofTechniqueBox
    unbox (UserProofTechniqueBox t) = t

data TransformEqualityUnitBox = TransformEqualityUnitBox (TransformH Equality ()) deriving Typeable

instance Extern (TransformH Equality ()) where
    type Box (TransformH Equality ()) = TransformEqualityUnitBox
    box = TransformEqualityUnitBox
    unbox (TransformEqualityUnitBox i) = i

interpProof :: Monad m => [Interp m ProofShellCommand]
interpProof =
  [ interp $ \ (RewriteCoreBox rr)            -> PCRewrite $ bothR $ extractR rr
  , interp $ \ (RewriteCoreTCBox rr)          -> PCRewrite $ bothR $ extractR rr
  , interp $ \ (BiRewriteCoreBox br)          -> PCRewrite $ bothR $ (extractR (forwardT br) <+ extractR (backwardT br))
  , interp $ \ (effect :: ShellEffect)        -> PCShell effect
  , interp $ \ (effect :: ScriptEffect)       -> PCScript effect
  , interp $ \ (StringBox str)                -> PCQuery (message str)
  , interp $ \ (query :: QueryFun)            -> PCQuery query
  , interp $ \ (RewriteEqualityBox r)         -> PCRewrite r
  , interp $ \ (TransformEqualityStringBox t) -> PCTransform t
  , interp $ \ (TransformEqualityUnitBox t)   -> PCUnit t
  , interp $ \ (UserProofTechniqueBox t)      -> PCUser t
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

quoteShow :: Show a => a -> String
quoteShow x = if all isScriptIdChar s then s else show s
    where s = show x

