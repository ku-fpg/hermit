{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, GADTs, TypeFamilies #-}

module HERMIT.Shell.KernelEffect 
    ( KernelEffect(..)
    , performKernelEffect
    ) where

import Control.Monad.State
import Control.Monad.Error

import Data.Monoid
import Data.Typeable

import HERMIT.Context
import HERMIT.Dictionary
import HERMIT.External
import qualified HERMIT.GHC as GHC
import HERMIT.Kernel (queryK)
import HERMIT.Kernel.Scoped hiding (abortS, resumeS)
import HERMIT.Kure
import HERMIT.Parser

import HERMIT.Plugin.Renderer

import HERMIT.PrettyPrinter.Common

import HERMIT.Shell.Types

-------------------------------------------------------------------------------

-- GADTs can't have docs on constructors. See Haddock ticket #43.
-- | KernelEffects are things that affect the state of the Kernel
--   - Apply a rewrite (giving a whole new lower-level AST).
--   - Change the current location using a computed path.
--   - Change the currect location using directions.
--   - Begin or end a scope.
--   - Delete an AST
--   - Run a precondition or other predicate that must not fail.
data KernelEffect :: * where
   Apply      :: (Injection GHC.ModGuts g, Walker HermitC g) => RewriteH g              -> KernelEffect
   Pathfinder :: (Injection GHC.ModGuts g, Walker HermitC g) => TransformH g LocalPathH -> KernelEffect
   Direction  ::                                                Direction               -> KernelEffect
   BeginScope ::                                                                           KernelEffect
   EndScope   ::                                                                           KernelEffect
   Delete     ::                                                SAST                    -> KernelEffect
   deriving Typeable

instance Extern KernelEffect where
   type Box KernelEffect = KernelEffect
   box i = i
   unbox i = i

-------------------------------------------------------------------------------

performKernelEffect :: (MonadCatch m, MonadError CLException m, MonadIO m, MonadState CommandLineState m) 
                    => KernelEffect -> ExprH -> m ()

performKernelEffect (Apply rr) expr = do
    st <- get

    let sk = cl_kernel st
        kEnv = cl_kernel_env st
        sast = cl_cursor st
        ppOpts = cl_pretty_opts st
        pp = pCoreTC $ cl_pretty st

    sast' <- prefixFailMsg "Rewrite failed: " $ applyS sk rr kEnv sast

    let commit = put (newSAST expr sast' st) >> showResult
        showResult = if cl_diffonly st then showDiff else showWindow
        showDiff = do doc1 <- queryS sk (liftPrettyH ppOpts pp) kEnv sast
                      doc2 <- queryS sk (liftPrettyH ppOpts pp) kEnv sast'
                      diffDocH (cl_pretty st) doc1 doc2 >>= cl_putStr

    if cl_corelint st
        then do ast' <- toASTS sk sast'
                liftIO (queryK (kernelS sk) ast' lintModuleT kEnv)
                >>= runKureM (\ warns -> putStrToConsole warns >> commit)
                             (\ errs  -> liftIO (deleteS sk sast') >> fail errs)
        else commit

performKernelEffect (Pathfinder t) expr = do
    st <- get
    -- An extension to the Path
    p <- prefixFailMsg "Cannot find path: " $ queryS (cl_kernel st) t (cl_kernel_env st) (cl_cursor st)
    ast <- prefixFailMsg "Path is invalid: " $ modPathS (cl_kernel st) (<> p) (cl_kernel_env st) (cl_cursor st)
    put $ newSAST expr ast st
    showWindow

performKernelEffect (Direction dir) expr = do
    st <- get
    ast <- prefixFailMsg "Invalid move: " $ modPathS (cl_kernel st) (moveLocally dir) (cl_kernel_env st) (cl_cursor st)
    put $ newSAST expr ast st
    showWindow

performKernelEffect BeginScope expr = do
    st <- get
    ast <- beginScopeS (cl_kernel st) (cl_cursor st)
    put $ newSAST expr ast st
    showWindow

performKernelEffect EndScope expr = do
    st <- get
    ast <- endScopeS (cl_kernel st) (cl_cursor st)
    put $ newSAST expr ast st
    showWindow

performKernelEffect (Delete sast) _ = gets cl_kernel >>= flip deleteS sast

-------------------------------------------------------------------------------
