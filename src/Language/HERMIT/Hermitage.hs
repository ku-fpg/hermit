{-# LANGUAGE RankNTypes, ScopedTypeVariables, FlexibleInstances, KindSignatures, GADTs #-}

-- A Hermitage is a place of quiet reflection.

module Language.HERMIT.Hermitage where

import GhcPlugins

import System.Environment
import System.Console.Editline

import Language.HERMIT.HermitEnv
import Language.HERMIT.HermitMonad
import Language.HERMIT.Types
import Language.HERMIT.Focus

-- abstact outside this module
data Hermitage c a = Hermitage
        { ageModGuts :: ModGuts
        , ageFocus   :: Focus c a
        , ageEnv     :: HermitEnv
        }
--        { close :: IO () }

-- Create a new Hermitage, does not return until the interaction
-- is completed. It is thread safe (any thread can call a 'Hermitage' function),
-- but not after the callback has terminated and returned.
new :: (Hermitage () ModGuts -> CoreM (Hermitage () ModGuts)) -> ModGuts -> CoreM ModGuts
new k modGuts = do
        modGuts' <- k (Hermitage modGuts InitialFocus initHermitEnv)
        return modGuts

-- Some of these do not need to be in IO,
-- but there are plans for async-access, memoization, etc,
-- so we'll stick them in the monad right now.

-- | What are the current module guts?
getModGuts :: Hermitage c a -> ModGuts
getModGuts age = ageModGuts age


-- | 'getForeground' gets the current 'blob' under consideraton.
getForeground :: Hermitage c a -> CoreM a
getForeground age = do undefined
--        let res = apply (focusTranslate (ageFocus age)) (ageEnv age)


 -- ageExtract age (ageModGuts age)

{-

-- | getBackground gets the background of the Hermitage,
-- getBackground


-}

-- this focuses in to a sub-expresssion. It will do error checking, hence the
-- need for the the CoreM.

focusHermitage :: Zoom a x
               -> Hermitage c a
               -> CoreM (Either HermitMessage (Hermitage (c,a) x))
focusHermitage zoom age = return $ Right $ Hermitage
        { ageModGuts    = ageModGuts age
        , ageFocus      = ageFocus age `AppendFocus` zoom
        , ageEnv = ageEnv age
        }

-- always works
unfocusHermitage :: Hermitage (c,a) x -> Hermitage c a
unfocusHermitage age = Hermitage
        { ageModGuts    = ageModGuts age
        , ageFocus      = unappendFocus $ ageFocus age
        , ageEnv        = ageEnv age
        }

applyRewrite :: Rewrite a -> Hermitage c a -> CoreM (Either HermitMessage (Hermitage c a))
applyRewrite = undefined

------------------------------------------------------------------
{-
data Focus :: * -> * -> * where
    FocusOnBinding :: Focus c (Bind Id) -- new focus is binding [group] containing a specific Id.
    FocusOnRhs     :: Id -> Focus c (Expr Id) -- new focus is left-hand-side of the binding of a specific Id.
    FocusOnExpr    :: (Expr Id -> Bool) -> Focus c (Expr Id) -- new focus using a expression predicated.
-}

focusOnBinding :: (Term a) => Zoom a (Bind Id)
focusOnBinding = error "focusOnBinding"

------------------------------------------------------------------

data HermitMessage
        = UnableToFocusMessage
        deriving (Show)

------------------------------------------------------------------

t = undefined :: Translate ModGuts Int
t2 = undefined :: Translate Int Bool
t3 = undefined :: Translate Bool Float
