module HERMIT.Pretty where

import GhcPlugins hiding (display)

import Control.Monad

import Language.HERMIT.Optimize
import Language.HERMIT.Plugin
import Language.HERMIT.Primitive.Navigation

import Language.Haskell.TH as TH

plugin :: Plugin
plugin = optimize $ \ fns -> after SpecConstr $
    forM_ fns $ \ fn -> at (considerName $ TH.mkName fn) display
