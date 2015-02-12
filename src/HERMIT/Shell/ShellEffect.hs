{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

module HERMIT.Shell.ShellEffect
    ( ShellEffect(..)
    , performShellEffect
    , dump
    ) where

import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.State (MonadState(..), gets)

import Data.Typeable

import HERMIT.External
import HERMIT.Kure
import HERMIT.Kernel.Scoped
import HERMIT.PrettyPrinter.Common

import HERMIT.Plugin.Renderer
import HERMIT.Plugin.Types

import HERMIT.Shell.Types

import System.IO

----------------------------------------------------------------------------------

data ShellEffect :: * where
    Abort      :: ShellEffect
    CLSModify  :: (CommandLineState -> IO CommandLineState) -> ShellEffect
    PluginComp :: PluginM () -> ShellEffect
    Continue   :: ShellEffect
    Dump       :: (CommandLineState -> TransformH CoreTC DocH) -> String -> String -> Int -> ShellEffect
    Resume     :: ShellEffect
    deriving Typeable

instance Extern ShellEffect where
    type Box ShellEffect = ShellEffect
    box i = i
    unbox i = i

----------------------------------------------------------------------------------

performShellEffect :: (MonadCatch m, CLMonad m) => ShellEffect -> m ()
performShellEffect Abort  = abort
performShellEffect Resume = gets cl_cursor >>= resume
performShellEffect Continue = get >>= continue
performShellEffect (Dump pp fileName renderer width) = dump pp fileName renderer width

performShellEffect (CLSModify f)  = get >>= liftAndCatchIO . f >>= put >> showWindow

performShellEffect (PluginComp m) = pluginM m >> showWindow

dump :: (MonadCatch m, MonadIO m, MonadState CommandLineState m) => (CommandLineState -> TransformH CoreTC DocH) -> String -> String -> Int -> m ()
dump pp fileName renderer width = do
    st <- get
    case lookup renderer shellRenderers of
      Just r -> do (_,doc) <- prefixFailMsg "Bad renderer option: " $ queryS (cl_kernel st) (pp st) (cl_kernel_env st) (cl_cursor st)
                   liftIO $ do h <- openFile fileName WriteMode
                               r h ((cl_pretty_opts st) { po_width = width }) (Right doc)
                               hClose h
      _ -> fail "dump: bad pretty-printer or renderer option"
