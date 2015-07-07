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
    , ShellEffectBox(..)
    , performShellEffect
    , dumpT
    , dump
    ) where

import Control.Monad.Error.Class (MonadError(..))
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Reader (ask)
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

data ShellEffect :: * -> * where
    Abort             :: ShellEffect ()
    CLSModify         :: CLT IO () -> ShellEffect ()
    PluginComp        :: PluginM () -> ShellEffect ()
    Continue          :: ShellEffect ()
    Resume            :: ShellEffect ()
    deriving Typeable

data ShellEffectBox where
    ShellEffectBox :: Typeable a => ShellEffect a -> ShellEffectBox
  deriving Typeable

instance Typeable a => Extern (ShellEffect a) where
    type Box (ShellEffect a) = ShellEffectBox
    box = ShellEffectBox
    unbox (ShellEffectBox i) = 
        case cast i of
          Just res -> res
          Nothing -> error "Extern -- unbox: casting of shell effect failed."

----------------------------------------------------------------------------------

performShellEffect :: (MonadCatch m, CLMonad m) => ShellEffect a -> m a
performShellEffect Abort  = abort
performShellEffect Resume = announceUnprovens >> gets cl_cursor >>= resume
performShellEffect Continue = announceUnprovens >> get >>= continue

performShellEffect (CLSModify m) = clm2clt m

performShellEffect (PluginComp m) = pluginM m

dumpT :: FilePath -> PrettyPrinter -> String -> Int -> TransformH DocH ()
dumpT fileName pp renderer width = do
    case lookup renderer shellRenderers of
      Just r -> do doc <- idR
                   liftIO $ do h <- openFile fileName WriteMode
                               r h ((pOptions pp) { po_width = width }) (Right doc)
                               hClose h
      _ -> fail "dump: bad renderer option"

dump :: FilePath -> PrettyPrinter -> String -> Int -> CLT IO ()
dump fileName pp renderer width = do
    st <- get
    env <- ask
    let st' = setPrettyOpts (setPretty st pp) $ (cl_pretty_opts st) { po_width = width }
    (er, _st'') <- runCLT env st' $ do
        pluginM (changeRenderer renderer)
        h <- liftIO $ openFile fileName WriteMode
        showWindowAlways (Just h)
        liftIO $ hClose h
    either throwError return er

