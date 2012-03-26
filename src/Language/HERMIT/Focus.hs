{-# LANGUAGE RankNTypes, ScopedTypeVariables, FlexibleInstances, KindSignatures,
    GADTs, DataKinds, TypeOperators, FlexibleContexts
  #-}

-- Our Focus module

{- If you see
ghc: panic! (the 'impossible' happened)
  (GHC version 7.4.1 for i386-apple-darwin):
	tyThingTyCon
    Data constructor `hermit-0.1:Language.HERMIT.Focus.:<{d r1U3}'
- Then cabal clean, and try again.

 Its a problem with the .hi file, and was fixed in HEAD, Jan 2012.
 -}


module Language.HERMIT.Focus where
{-
        ( Context(..)
        , Focus(..)
        , Zoom
        , unappendFocus
        , focusRewrite
        , focusTranslate
        , focusOnBinding
        , ) where
-}
import GhcPlugins

import Language.HERMIT.HermitEnv
import Language.HERMIT.HermitMonad
import Language.HERMIT.Types
import Language.HERMIT.KURE

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
-- Zoom says, if you have 'b', I can zoom there from an 'a'.
data Zoom a b = Zoom
        { rewriteD :: Rewrite b -> Rewrite a
        , projectD :: Translate a [b]
        }

-- | 'unappendFocus' removes the top zoom, and throws it away.
unappendFocus :: Focus (b :< cxt) c -> Focus cxt b
unappendFocus (AppendFocus focus _) = focus

focusRewrite :: Focus cxt b -> Rewrite b -> Rewrite ModGuts
focusRewrite InitialFocus      rr = rr
focusRewrite (AppendFocus f z) rr = focusRewrite f (rewriteD z rr)

focusTranslate :: Focus cxt b -> Translate ModGuts [b]
focusTranslate InitialFocus      = pureT (\ x -> [x])
focusTranslate (AppendFocus f z) = focusTranslate f >>> listU (projectD z)

------------------------------------------------------------------

{-
-- Just ideas for later regarding types of making Zooms.
data Focus :: * -> * -> * where
    FocusOnBinding :: Focus c (Bind Id) -- new focus is binding [group] containing a specific Id.
    FocusOnRhs     :: Id -> Focus c (Expr Id) -- new focus is left-hand-side of the binding of a specific Id.
    FocusOnExpr    :: (Expr Id -> Bool) -> Focus c (Expr Id) -- new focus using a expression predicated.
-}

-- Right now, this searches *everything* for the match. Later, we'll
-- have some way of optimizing this to be more focused (pun) and efficent.

focusOnBinding :: (Generic a ~ Generic (Bind Id), Term a) => Zoom a (Bind Id)
focusOnBinding = focusOn $ \ bnds ->
        case bnds of
          NonRec {} | True -> True
          Rec bds' -> True


focusOn
  :: ( Term a, Term b
     , Generic a ~ Generic b
     , Term (Generic a)
     , Term (Generic b)
     )
  => (b -> Bool) -> Zoom a b
focusOn pred = Zoom
        { rewriteD = extractR . focusOnRewrite pred
        , projectD = extractU $ focusOnTranslate pred
        }

focusOnRewrite :: (Term a, Term b, a ~ Generic a, Generic a ~ Generic b)
               => (b -> Bool) -> Rewrite b -> Rewrite (Generic a)
focusOnRewrite pred rr =
        promoteR (acceptR pred >-> rr) <+
        allR (focusOnRewrite pred rr)

focusOnTranslate :: (Term a, Term b, a ~ Generic a, Generic a ~ Generic b)
               => (b -> Bool) -> Translate (Generic a) [b]
focusOnTranslate pred =
        promoteU (acceptR pred >-> pureT (\ a -> [a]))  <+
        crushU (focusOnTranslate pred)

------------------------------------------------------------------
