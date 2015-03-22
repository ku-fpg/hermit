{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}

module HERMIT.Shell.Proof
    ( externals
    , UserProofTechnique
    , userProofTechnique
    , withProofExternals
    , performProofShellCommand
    , forceProofs
    , ProofShellCommand(PCEnd)
    , ProofReason(UserProof)
    ) where

import Control.Arrow hiding (loop, (<+>))
import Control.Monad (forM_)
import Control.Monad.Error.Class (MonadError(..))
import Control.Monad.State (MonadState, modify, gets)

import Data.Dynamic
import Data.Monoid

import HERMIT.Context
import HERMIT.External
import HERMIT.Kernel
import HERMIT.Kure
import HERMIT.Lemma
import HERMIT.Monad
import HERMIT.Parser
import HERMIT.Syntax

import HERMIT.Dictionary.Reasoning hiding (externals)

import HERMIT.Shell.ShellEffect
import HERMIT.Shell.Types

--------------------------------------------------------------------------------------------------------

-- | Externals that get us into the prover shell.
externals :: [External]
externals = map (.+ Proof)
    [ external "prove-lemma" (CLSModifyAndShow . interactiveProofIO)
        [ "Proof a lemma interactively." ]
    ]

-- | Externals that are added to the dictionary only when in interactive proof mode.
proof_externals :: [External]
proof_externals = map (.+ Proof)
    [ external "lemma" (PCEnd . LemmaProof Obligation)
        [ "Prove lemma by asserting it is alpha-equivalent to an already proven lemma." ]
    , external "lemma-unsafe" (PCEnd . LemmaProof UnsafeUsed)
        [ "Prove lemma by asserting it is alpha-equivalent to an already proven lemma." ] .+ Unsafe
    , external "end-proof" (PCEnd Reflexivity)
        [ "check for alpha-equality, marking the lemma as proven" ]
    , external "end-case" (PCEnd Reflexivity)
        [ "check for alpha-equality, marking the proof case as proven" ]
    , external "assume" (PCEnd UserAssume)
        [ "mark lemma as assumed" ]
    ]

--------------------------------------------------------------------------------------------------------

-- | Top level entry point!
interactiveProofIO :: LemmaName -> CommandLineState -> IO (Either CLException CommandLineState)
interactiveProofIO nm s = do
    (r,st) <- runCLT s $ do
                ps <- getProofStackEmpty
                let t :: TransformH x (HermitC,Lemma)
                    t = contextT &&& getLemmaByNameT nm
                (c,l) <- case ps of
                            [] -> queryInFocus (t :: TransformH Core (HermitC,Lemma))
                                               (Always $ "prove-lemma " ++ quoteShow nm)
                            todo : _ -> queryInFocus (inProofFocusT todo t) Never
                pushProofStack $ Unproven nm l c mempty
    return $ fmap (const st) r

withProofExternals :: (MonadError CLException m, MonadState CommandLineState m) => m a -> m a
withProofExternals comp = do
    (es,sf) <- gets (cl_externals &&& cl_safety)
    let pes = filterSafety sf proof_externals
        -- commands with same same in proof_externals will override those in normal externals
        newEs = pes ++ filter ((`notElem` (map externName pes)) . externName) es
        reset s = s { cl_externals = es }
    modify $ \ s -> s { cl_externals = newEs }
    r <- comp `catchError` (\case CLContinue s -> continue (reset s)
                                  other        -> modify reset >> throwError other)
    modify reset
    return r

forceProofs :: (MonadCatch m, CLMonad m) => m ()
forceProofs = do
    (c,nls) <- queryInFocus (contextT &&& getObligationNotProvenT :: TransformH Core (HermitC, [NamedLemma])) Never
    todos <- getProofStackEmpty
    let already = map ptName todos
        nls' = [ nl | nl@(nm,_) <- nls, not (nm `elem` already) ]
    if null nls'
    then return ()
    else do
        c' <- case todos of
                todo : _ -> queryInFocus (inProofFocusT todo contextT) Never
                _        -> return c
        forM_ nls' $ \ (nm,l) -> pushProofStack (Unproven nm l c' mempty)

-- | Verify that the lemma has been proven. Throws an exception if it has not.
endProof :: (MonadCatch m, CLMonad m) => ProofReason -> ExprH -> m ()
endProof reason expr = do
    Unproven nm (Lemma q _ _ temp) c _ : _ <- getProofStack
    let msg = "The two sides of " ++ quoteShow nm ++ " are not alpha-equivalent."
        deleteOr tr = if temp then constT (deleteLemma nm) else tr
        t = case reason of
                UserAssume -> deleteOr (markLemmaProvenT nm Assumed)
                Reflexivity -> setFailMsg msg (do tryR (extractR simplifyQuantifiedR) >>> verifyQuantifiedT
                                                  deleteOr (markLemmaProvenT nm Proven))
                LemmaProof u nm' -> verifyEquivalentT u nm' >> deleteOr (markLemmaProvenT nm Proven)
                UserProof up -> let UserProofTechnique tr = up
                                in extractT tr >> deleteOr (markLemmaProvenT nm Proven)
    queryInFocus (constT (applyT t c q) :: TransformH Core ())
                 (Always $ unparseExprH expr ++ " -- proven " ++ quoteShow nm)
    _ <- popProofStack
    cl_putStrLn $ "Successfully proven: " ++ show nm

-- Note [Query]
-- We want to do our proof in the current context of the shell, whatever that is,
-- so we run them using queryInFocus below. This has the benefit that proof commands
-- can generate additional lemmas, and add to the version history.
performProofShellCommand :: (MonadCatch m, CLMonad m)
                         => ProofShellCommand -> ExprH -> m ()
performProofShellCommand cmd expr = go cmd >> ifM isRunningScript (return ()) (showWindow Nothing)
    where go (PCEnd why)          = endProof why expr

data ProofShellCommand
    = PCEnd ProofReason
    deriving Typeable

data ProofReason = UserProof UserProofTechnique -- ^ Run the technique, mark Proven if succeeds
                 | UserAssume                   -- ^ Assume
                 | Reflexivity                  -- ^ Check for alpha-equivalence first
                 | LemmaProof Used LemmaName    -- ^ Used should be 'UnsafeUsed' or 'Obligation'

-- keep abstract to avoid breaking things if we modify this later
newtype UserProofTechnique = UserProofTechnique (TransformH LCoreTC ())
    deriving Typeable

userProofTechnique :: TransformH LCoreTC () -> UserProofTechnique
userProofTechnique = UserProofTechnique

instance Extern ProofShellCommand where
    type Box ProofShellCommand = ProofShellCommand
    box i = i
    unbox i = i

instance Extern UserProofTechnique where
    type Box UserProofTechnique = UserProofTechnique
    box i = i
    unbox i = i
