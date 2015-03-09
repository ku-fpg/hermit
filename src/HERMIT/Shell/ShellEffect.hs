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
    , dumpT
    ) where

import Control.Monad.Error.Class (MonadError(..))
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.State (MonadState(..), gets)

import Data.Typeable

import HERMIT.External
import HERMIT.Kure
import HERMIT.PrettyPrinter.Common

import HERMIT.Plugin.Renderer
import HERMIT.Plugin.Types

import HERMIT.Shell.Types

import System.IO

----------------------------------------------------------------------------------

data ShellEffect :: * where
    Abort      :: ShellEffect
    CLSModify  :: (CommandLineState -> IO (Either CLException CommandLineState)) -> ShellEffect
    PluginComp :: PluginM () -> ShellEffect
    Continue   :: ShellEffect
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

performShellEffect (CLSModify f)  = get >>= liftAndCatchIO . f >>= either throwError put

performShellEffect (PluginComp m) = pluginM m

dumpT :: FilePath -> PrettyPrinter -> String -> Int -> TransformH DocH ()
dumpT fileName pp renderer width = do
    case lookup renderer shellRenderers of
      Just r -> do doc <- idR
                   liftIO $ do h <- openFile fileName WriteMode
                               r h ((pOptions pp) { po_width = width }) (Right doc)
                               hClose h
      _ -> fail "dump: bad renderer option"
