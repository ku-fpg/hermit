{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude #-}
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
    , ProofReason(UserProof, UserAssume, Reflexivity)
    ) where

import Control.Arrow hiding (loop, (<+>))
import Control.Concurrent.STM
import Control.Monad (unless) -- requires Monad context on GHC 7.8
import Control.Monad.Compat hiding (unless)
import Control.Monad.Error.Class (MonadError(..))
import Control.Monad.IO.Class
import Control.Monad.Reader (asks)
import Control.Monad.State (MonadState(get), modify, gets)

import Data.Dynamic
import Data.Function (on)
import Data.List.Compat (nubBy)

import HERMIT.Context
import HERMIT.External
import HERMIT.GHC
import HERMIT.Kernel
import HERMIT.Kure
import HERMIT.Lemma
import HERMIT.Parser
import HERMIT.Syntax

import HERMIT.Dictionary.Reasoning hiding (externals)

import HERMIT.Plugin.Types
import HERMIT.Shell.ShellEffect
import HERMIT.Shell.Types

import Prelude.Compat

--------------------------------------------------------------------------------------------------------

-- | Externals that get us into the prover shell.
externals :: [External]
externals = map (.+ Proof)
    [ external "prove-lemma" (\nm -> CLSModify $ interactiveProof nm >> showWindow Nothing)
        [ "Proof a lemma interactively." ]
    ]

-- | Externals that are added to the dictionary only when in interactive proof mode.
proof_externals :: [External]
proof_externals = map (.+ Proof)
    [ external "end-proof" (PCEnd Reflexivity)
        [ "check for alpha-equality, marking the lemma as proven" ]
    , external "end-case" (PCEnd Reflexivity)
        [ "check for alpha-equality, marking the proof case as proven" ]
    , external "assume" (PCEnd UserAssume)
        [ "mark lemma as assumed" ]
    ]

--------------------------------------------------------------------------------------------------------

-- | Top level entry point!
interactiveProof :: LemmaName -> CLT IO ()
interactiveProof nm = do
    ps <- getProofStackEmpty
    let t :: TransformH x (HermitC,Lemma)
        t = contextT &&& getLemmaByNameT nm
    (c,l) <- case ps of
                [] -> queryInFocus (t :: TransformH Core (HermitC,Lemma))
                                   (Always $ "prove-lemma " ++ quoteShow nm)
                todo : _ -> queryInFocus (inProofFocusT todo t) Never
    pushProofStack $ Unproven nm l c mempty

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
    k <- asks pr_kernel
    st <- get
    ls <- liftIO $ atomically $ swapTVar (cl_templemmas st) []
    let snd3 (_,y,_) = y
        nls = nubBy ((==) `on` snd3) ls
    unless (null nls) $ do
        (_,topc) <- queryK k (arr topLevelHermitC) Never (cl_kernel_env st) (cl_cursor st)
        let chooseC c cl = if all (inScope topc) (varSetElems (freeVarsClause cl)) then (True,topc) else (False,c)
            nls' = [ (chooseC c (lemmaC l), nm, l) | (c,nm,l) <- nls ]
            nonTemp = [ (nm,l) | ((True,_),nm,l) <- nls' ]
        unless (null nonTemp) $
            queryInFocus (insertLemmasT nonTemp :: TransformH LCore ())
                         (Always $ "-- recording obligations as lemmas : " ++ unwords (map (show.fst) (reverse nonTemp)))
        forM_ nls' $ \ ((_,c),nm,l) -> do
            cl_putStrLn $ "Forcing obligation: " ++ show nm
            pushProofStack (Unproven nm l c mempty)
        showWindow Nothing

-- | Verify that the lemma has been proven. Throws an exception if it has not.
endProof :: (MonadCatch m, CLMonad m) => ProofReason -> ExprH -> m ()
endProof reason expr = do
    Unproven nm (Lemma q _ _) c _ : _ <- getProofStack
    let msg = "The two sides of " ++ quoteShow nm ++ " are not alpha-equivalent."
        t = case reason of
                UserAssume -> markLemmaProvenT nm Assumed
                Reflexivity -> setFailMsg msg (do tryR (extractR simplifyClauseR) >>> verifyClauseT
                                                  markLemmaProvenT nm Proven)
                UserProof up -> let UserProofTechnique tr = up
                                in extractT tr >> markLemmaProvenT nm Proven
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
performProofShellCommand cmd expr = go cmd >> showWindow Nothing
    where go (PCEnd why)          = endProof why expr

data ProofShellCommand
    = PCEnd ProofReason
    deriving Typeable

data ProofReason = UserProof UserProofTechnique -- ^ Run the technique, mark Proven if succeeds
                 | UserAssume                   -- ^ Assume
                 | Reflexivity                  -- ^ Check for alpha-equivalence first
  deriving Typeable

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
