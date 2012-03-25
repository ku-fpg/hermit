{-# LANGUAGE RankNTypes, ScopedTypeVariables, FlexibleInstances, KindSignatures, GADTs, DataKinds, TypeOperators #-}

-- Our Focus module

{- If you see
ghc: panic! (the 'impossible' happened)
  (GHC version 7.4.1 for i386-apple-darwin):
	tyThingTyCon
    Data constructor `hermit-0.1:Language.HERMIT.Focus.:<{d r1U3}'
- Then cabal clean, and try again.

 Its a problem with the .hi file, and was fixed in HEAD, Jan 2012.
 -}


module Language.HERMIT.Focus
        ( Context(..)
        , Focus(..)
        , Zoom
        , unappendFocus
        , focusRewrite
        , focusTranslate
        , focusOnBinding
        , ) where

import GhcPlugins

import Language.HERMIT.HermitEnv
import Language.HERMIT.HermitMonad
import Language.HERMIT.Types

import Control.Arrow
import qualified Control.Category as Cat

-- Context is *Kind*.
data Context where
        Everything :: Context
        (:<) :: a -> Context -> Context

infixr 5 :<

data Focus :: Context -> * -> * where
    InitialFocus ::                            Focus Everything ModGuts
    AppendFocus  :: Focus cxt b -> Zoom b c -> Focus (b :< cxt) c

-- Invarient, The project gets the same thing as the rewrite transformes
-- Zoom says, if you have 'b', I can zoom there, and the 'a' is our context stack.
data Zoom a b = Zoom
        { rewriteD :: Rewrite b -> Rewrite a
        , projectD :: Translate a b
        }

-- | 'unappendFocus' removes the top zoom, and throws it away.
unappendFocus :: Focus (b :< cxt) c -> Focus cxt b
unappendFocus (AppendFocus focus _) = focus

focusRewrite :: Focus cxt b -> Rewrite b -> Rewrite ModGuts
focusRewrite InitialFocus      rr = rr
focusRewrite (AppendFocus f z) rr = focusRewrite f (rewriteD z rr)

focusTranslate :: Focus cxt b -> Translate ModGuts b
focusTranslate InitialFocus      = Cat.id
focusTranslate (AppendFocus f z) = focusTranslate f >>> projectD z

------------------------------------------------------------------

{-
-- Just ideas for later regarding types of making Zooms.
data Focus :: * -> * -> * where
    FocusOnBinding :: Focus c (Bind Id) -- new focus is binding [group] containing a specific Id.
    FocusOnRhs     :: Id -> Focus c (Expr Id) -- new focus is left-hand-side of the binding of a specific Id.
    FocusOnExpr    :: (Expr Id -> Bool) -> Focus c (Expr Id) -- new focus using a expression predicated.
-}

focusOnBinding :: (Term a) => Zoom a (Bind Id)
focusOnBinding = error "focusOnBinding"

------------------------------------------------------------------
