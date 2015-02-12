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
import Control.Monad.State (MonadState(get, put), modify)
import Control.Monad.Trans.Class (lift)

import Data.Char (isSpace)
import Data.Dynamic
import Data.List (delete)
import Data.String (fromString)

import HERMIT.Core
import HERMIT.Equality
import HERMIT.External
import HERMIT.GHC hiding (settings, (<>), text, sep, (<+>), ($+$), nest)
import HERMIT.Kernel.Scoped
import HERMIT.Kure
import HERMIT.Monad
import HERMIT.Parser
import HERMIT.Utilities

import HERMIT.Dictionary.GHC hiding (externals)
import HERMIT.Dictionary.Induction
import HERMIT.Dictionary.Reasoning hiding (externals)

import HERMIT.Plugin.Types
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
    st <- get
    (_,doc) <- queryS (cl_kernel st) (return lem >>> liftPrettyH (pOptions (cl_pretty st)) (ppLemmaT (cl_pretty st) nm) :: TransformH Core DocH) (cl_kernel_env st) (cl_cursor st)
    liftIO $ cl_render st stdout (cl_pretty_opts st) (Right doc)

--------------------------------------------------------------------------------------------------------

type NamedLemma = (LemmaName, Lemma)

interactiveProofIO :: LemmaName -> CommandLineState -> IO (Either CLException CommandLineState)
interactiveProofIO nm s = do
    let st = cl_pstate s
    (_,l) <- queryS (ps_kernel st) (getLemmaByNameT nm :: TransformH Core Lemma) (mkKernelEnv st) (ps_cursor st)
    (r,s') <- runCLT s $ interactiveProof True False (nm,l)
    return $ fmap (const s') r

interactiveProof :: forall m. (MonadCatch m, MonadException m, CLMonad m) => Bool -> Bool -> NamedLemma -> m ()
interactiveProof topLevel isTemporary lem@(nm,_) = do
    origSt <- get
    origEs <- addProofExternals topLevel

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
                                            else lift (evalProofScript l line `catchM` (\msg -> cl_putStrLn msg >> return l)) >>= loop
                Just e -> lift (runExprH l e `catchM` (\msg -> setRunningScript Nothing >> cl_putStrLn msg >> return l)) >>= loop

    -- Display a proof banner?

    -- Start the CLI
    let settings = setComplete (completeWordWithPrev Nothing ws_complete shellComplete) defaultSettings
        cleanup s = put (s { cl_externals = origEs })
    catchError (runInputT settings (loop lem))
               (\case
                    CLAbort        -> cleanup origSt >> unless topLevel abort -- abandon proof attempt, bubble out to regular shell
                    CLContinue st' -> do
                        cl_putStrLn $ "Successfully proven: " ++ show nm
                        if isTemporary
                        then cleanup st'    -- successfully proven
                        else do (sast,()) <- queryS (cl_kernel st')
                                               (modifyLemmaT nm id idR (const True) id :: TransformH Core ())
                                               (mkKernelEnv $ cl_pstate st')
                                               (cl_cursor st')
                                cleanup $ newSAST (CmdName "proven") sast st'

                    CLError msg    -> fail $ "Prover error: " ++ msg
                    _              -> fail "unsupported exception in interactive prover")

addProofExternals :: MonadState CommandLineState m => Bool -> m [External]
addProofExternals topLevel = do
    st <- get
    let es = cl_externals st
        -- commands with same same in proof_externals will override those in normal externals
        newEs = proof_externals ++ filter ((`notElem` (map externName proof_externals)) . externName) es
    when topLevel $ modify $ \ s -> s { cl_externals = newEs }
    return es

evalProofScript :: (MonadCatch m, MonadException m, CLMonad m) => NamedLemma -> String -> m NamedLemma
evalProofScript lem = parseScriptCLT >=> foldM runExprH lem

runExprH :: (MonadCatch m, MonadException m, CLMonad m) => NamedLemma -> ExprH -> m NamedLemma
runExprH lem expr = prefixFailMsg ("Error in expression: " ++ unparseExprH expr ++ "\n")
                  $ interpExprH interpProof expr >>= performProofShellCommand lem

-- | Verify that the lemma has been proven. Throws an exception if it has not.
endProof :: (MonadCatch m, MonadError CLException m, MonadIO m, MonadState CommandLineState m) => NamedLemma -> m ()
endProof (nm, Lemma eq _ _) = do
    st <- get

    let sk = cl_kernel st
        kEnv = cl_kernel_env st
        sast = cl_cursor st

    -- Why do a query? We want to do our proof in the current context of the shell, whatever that is.
    (_,b) <- (queryS sk (return eq >>> testM verifyEqualityT :: TransformH Core Bool) kEnv sast)
    if b then continue st else fail $ "The two sides of " ++ show nm ++ " are not alpha-equivalent."

performProofShellCommand :: (MonadCatch m, MonadException m, CLMonad m) => NamedLemma -> ProofShellCommand -> m NamedLemma
performProofShellCommand lem@(nm, Lemma eq p u) = go
    where go (PCRewrite rr)         = do
                st <- get
                let sk = cl_kernel st
                    kEnv = cl_kernel_env st
                    sast = cl_cursor st

                -- Why do a query? We want to do our proof in the current context of the shell, whatever that is.
                (sast', eq') <- queryS sk (return eq >>> rr >>> (bothT lintExprT >> idR) :: TransformH Core Equality) kEnv sast
                modify $ setCursor sast'
                return (nm, Lemma eq' p u)
          go (PCTransform t)      = do
                st <- get
                let sk = cl_kernel st
                    kEnv = cl_kernel_env st
                    sast = cl_cursor st

                -- Why do a query? See above.
                (sast', res) <- queryS sk (return eq >>> t :: TransformH Core String) kEnv sast
                modify $ setCursor sast'
                cl_putStrLn res
                return lem
          go (PCUnit t)      = do
                st <- get
                let sk = cl_kernel st
                    kEnv = cl_kernel_env st
                    sast = cl_cursor st

                -- Why do a query? See above.
                (sast', ()) <- queryS sk (return eq >>> t :: TransformH Core ()) kEnv sast
                modify $ setCursor sast'
                return lem
          go (PCInduction idPred) = performInduction lem idPred
          go (PCShell effect)     = performShellEffect effect >> return lem
          go (PCScript effect)    = do
                lemVar <- liftIO $ newMVar lem -- couldn't resist that name
                let lemHack e = liftIO (takeMVar lemVar) >>= flip runExprH e >>= liftIO . putMVar lemVar
                performScriptEffect lemHack effect
                liftIO $ takeMVar lemVar
          go (PCQuery query)      = performQuery query (error "PCQuery ExprH") >> return lem
          go (PCUser prf)         = let UserProofTechnique t = prf in -- may add more constructors later
             do
                st <- get
                -- Why do a query? We want to do our proof in the current context of the shell, whatever that is.
                (sast',()) <- queryS (cl_kernel st) (return eq >>> t :: TransformH Core ()) (cl_kernel_env st) (cl_cursor st)
                continue $ setCursor sast' st -- note: we assume that if 't' completes without failing, the lemma is proved, we don't actually check
                return lem       -- never reached
          go PCEnd                = endProof lem >> return lem
          go (PCUnsupported s)    = cl_putStrLn (s ++ " command unsupported in proof mode.") >> return lem

performInduction :: (MonadCatch m, MonadException m, CLMonad m) => NamedLemma -> (Id -> Bool) -> m NamedLemma
performInduction lem@(nm, Lemma eq@(Equality bs lhs rhs) _ _) idPred = do
    st <- get
    let sk = cl_kernel st
        kEnv = cl_kernel_env st
        sast = cl_cursor st

    i <- setFailMsg "specified identifier is not universally quantified in this equality lemma." $ soleElement (filter idPred bs)
    -- Why do a query? We want to do our proof in the current context of the shell, whatever that is.
    (_,cases) <- queryS sk (inductionCaseSplit bs i lhs rhs :: TransformH Core [(Maybe DataCon,[Var],CoreExpr,CoreExpr)]) kEnv sast

    forM_ cases $ \ (mdc,vs,lhsE,rhsE) -> do

        -- TODO rethink the remake.discardUniVars
        let vs_matching_i_type = filter (typeAlphaEq (varType i) . varType) vs
            remake (Equality bndrs l r) = mkEquality bndrs l r

        -- Generate list of specialized induction hypotheses for the recursive cases.
        eqs <- forM vs_matching_i_type $ \ i' ->
                    liftM (remake.discardUniVars) $ instantiateEqualityVar (==i) (Var i') [] eq

        let nms = [ fromString ("ind-hyp-" ++ show n) | n :: Int <- [0..] ]
            hypLemmas = zip nms $ zipWith3 Lemma eqs (repeat True) (repeat False)
            lemmaName = fromString $ show nm ++ "-induction-on-"
                                             ++ unqualifiedName i ++ "-case-"
                                             ++ maybe "undefined" unqualifiedName mdc
            caseLemma = Lemma (Equality (delete i bs ++ vs) lhsE rhsE) False False

        -- this is pretty hacky
        sast' <- addLemmas hypLemmas  -- add temporary lemmas
        interactiveProof False True (lemmaName,caseLemma) -- recursion!
        modify $ setCursor sast' -- discard temporary lemmas

    get >>= continue
    return lem -- this is never reached, but the type says we need it.

addLemmas :: (MonadCatch m, MonadError CLException m, MonadIO m, MonadState CommandLineState m)
          => [NamedLemma] -> m SAST
addLemmas lems = do
    ifM isRunningScript (return ()) $ forM_ lems printLemma
    let addAllAtOnceT :: TransformH Core ()
        addAllAtOnceT = constT $ forM_ lems $ \ (nm,l) -> insertLemma nm l

    st <- get
    (sast,()) <- queryS (cl_kernel st) addAllAtOnceT (mkKernelEnv $ cl_pstate st) (cl_cursor st)
    put $ newSAST (CmdName "adding lemmas") sast st

    -- return original SAST
    return $ cl_cursor st

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
  , interp $ \ (TransformCoreStringBox _tt)   -> PCUnsupported "TransformCoreStringBox"
  , interp $ \ (TransformCoreTCStringBox _tt) -> PCUnsupported "TransformCoreTCStringBox"
  , interp $ \ (TransformCoreCheckBox _tt)    -> PCUnsupported "TransformCoreCheckBox"
  , interp $ \ (TransformCoreTCCheckBox _tt)  -> PCUnsupported "TransformCoreTCCheckBox"
  , interp $ \ (_effect :: KernelEffect)      -> PCUnsupported "KernelEffect"
  ]

