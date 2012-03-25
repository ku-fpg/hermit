{-# LANGUAGE RankNTypes, ScopedTypeVariables, FlexibleInstances, KindSignatures, GADTs #-}

-- A Hermitage is a place of quiet reflection.

module Language.HERMIT.Focus where

import GhcPlugins

import Language.HERMIT.HermitEnv
import Language.HERMIT.HermitMonad
import Language.HERMIT.Types

import Control.Arrow
import qualified Control.Category as Cat

data Focus :: * -> * -> * where
    InitialFocus ::                          Focus () ModGuts
    AppendFocus  :: Focus a b -> Zoom b c -> Focus (a,b) c

-- Invarient, The project gets the same thing as the rewrite transformes
-- Zoom says, if you have 'b', I can zoom there, and the 'a' is our context stack.
data Zoom a b = Zoom
        { rewriteD :: Rewrite b -> Rewrite a
        , projectD :: Translate a b
        }

-- | 'unappendFocus' removes the top zoom, and throws it away.
unappendFocus :: Focus (a,b) c -> Focus a b
unappendFocus (AppendFocus focus _) = focus

focusRewrite :: Focus a b -> Rewrite b -> Rewrite ModGuts
focusRewrite InitialFocus      rr = rr
focusRewrite (AppendFocus f z) rr = focusRewrite f (rewriteD z rr)

focusTranslate :: Focus a b -> Translate ModGuts b
focusTranslate InitialFocus      = Cat.id
focusTranslate (AppendFocus f z) = focusTranslate f >>> projectD z
