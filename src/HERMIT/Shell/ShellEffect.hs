{-# LANGUAGE CPP, KindSignatures, GADTs, FlexibleContexts, TypeFamilies,
             DeriveDataTypeable, GeneralizedNewtypeDeriving, LambdaCase,
             MultiParamTypeClasses, ScopedTypeVariables #-}

module HERMIT.Shell.ShellEffect 
    ( ShellEffect(..)
    , performShellEffect
    ) where

import Control.Monad.Error
import Control.Monad.State

import Data.Typeable

import HERMIT.Dictionary
import HERMIT.External
import HERMIT.Kure
import HERMIT.Kernel.Scoped
import HERMIT.PrettyPrinter.Common

import HERMIT.Plugin.Renderer
import HERMIT.Plugin.Types

import HERMIT.Shell.Types

import System.IO

----------------------------------------------------------------------------------

data ShellEffect
    = Abort -- ^ Abort GHC
    | CLSModify (CommandLineState -> IO CommandLineState) -- ^ Modify shell state
    | PluginComp (PluginM ())
    | Continue -- ^ exit the shell, but don't abort/resume
    | Dump String String Int
    | Resume
    deriving Typeable

instance Extern ShellEffect where
    type Box ShellEffect = ShellEffect
    box i = i
    unbox i = i

{-
instance ShellCommandSet ShellEffect () () where
    performCommand e () = performShellEffect e
-}

----------------------------------------------------------------------------------

performShellEffect :: (MonadCatch m, MonadError CLException m, MonadIO m, MonadState CommandLineState m) => ShellEffect -> m ()
performShellEffect Abort  = abort
performShellEffect Resume = do
    st <- get
    sast' <- applyS (cl_kernel st) occurAnalyseAndDezombifyR (cl_kernel_env st) (cl_cursor st)
    resume sast'

performShellEffect Continue = get >>= continue
performShellEffect (Dump fileName renderer width) = do
    st <- get
    case lookup renderer shellRenderers of
      Just r -> do doc <- prefixFailMsg "Bad renderer option: " $
                            queryS (cl_kernel st) (liftPrettyH (cl_pretty_opts st) $ cl_pretty st) (cl_kernel_env st) (cl_cursor st)
                   liftIO $ do h <- openFile fileName WriteMode
                               r h ((cl_pretty_opts st) { po_width = width }) (Right doc)
                               hClose h
      _ -> fail "dump: bad pretty-printer or renderer option"

performShellEffect (CLSModify f) = get >>= liftAndCatchIO . f >>= put >> showWindow

performShellEffect (PluginComp m) = pluginM m >> showWindow
