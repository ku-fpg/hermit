{-# LANGUAGE ConstraintKinds, DeriveDataTypeable, FlexibleContexts, LambdaCase, TypeFamilies #-}

module HERMIT.Shell.KernelEffect
    ( KernelEffect(..)
    , performKernelEffect
    , applyRewrite
    , setPath
    , goDirection
    , beginScope
    , endScope
    , deleteSAST
    ) where

import Control.Monad.State

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

-- | KernelEffects are things that affect the state of the Kernel
data KernelEffect = Direction  Direction -- Change the currect location using directions.
                  | BeginScope           -- Begin scope.
                  | EndScope             -- End scope.
                  | Delete     SAST      -- Delete an AST
   deriving Typeable

instance Extern KernelEffect where
   type Box KernelEffect = KernelEffect
   box i = i
   unbox i = i

performKernelEffect :: (MonadCatch m, CLMonad m) => ExprH -> KernelEffect -> m ()
performKernelEffect e = \case
                            Direction dir -> goDirection dir e
                            BeginScope    -> beginScope e
                            EndScope      -> endScope e
                            Delete sast   -> deleteSAST sast

-------------------------------------------------------------------------------

applyRewrite :: (Injection GHC.ModGuts g, Walker HermitC g, MonadCatch m, CLMonad m)
             => RewriteH g -> ExprH -> m ()
applyRewrite rr expr = do
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

setPath :: (Injection GHC.ModGuts g, Walker HermitC g, MonadCatch m, CLMonad m)
        => TransformH g LocalPathH -> ExprH -> m ()
setPath t expr = do
    st <- get
    -- An extension to the Path
    p <- prefixFailMsg "Cannot find path: " $ queryS (cl_kernel st) t (cl_kernel_env st) (cl_cursor st)
    ast <- prefixFailMsg "Path is invalid: " $ modPathS (cl_kernel st) (<> p) (cl_kernel_env st) (cl_cursor st)
    put $ newSAST expr ast st
    showWindow

goDirection :: (MonadCatch m, CLMonad m) => Direction -> ExprH -> m ()
goDirection dir expr = do
    st <- get
    ast <- prefixFailMsg "Invalid move: " $ modPathS (cl_kernel st) (moveLocally dir) (cl_kernel_env st) (cl_cursor st)
    put $ newSAST expr ast st
    showWindow

beginScope :: (MonadCatch m, CLMonad m) => ExprH -> m ()
beginScope expr = do
    st <- get
    ast <- beginScopeS (cl_kernel st) (cl_cursor st)
    put $ newSAST expr ast st
    showWindow

endScope :: (MonadCatch m, CLMonad m) => ExprH -> m ()
endScope expr = do
    st <- get
    ast <- endScopeS (cl_kernel st) (cl_cursor st)
    put $ newSAST expr ast st
    showWindow

deleteSAST :: (MonadCatch m, CLMonad m) => SAST -> m ()
deleteSAST sast = gets cl_kernel >>= flip deleteS sast

-------------------------------------------------------------------------------
