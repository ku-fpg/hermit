{-# LANGUAGE RankNTypes, ScopedTypeVariables, FlexibleInstances, KindSignatures, GADTs, DataKinds, TypeOperators #-}

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
data Hermitage (c :: CXT) a = Hermitage
        { ageModGuts :: ModGuts
        , ageFocus   :: Focus c a
        , ageEnv     :: HermitEnv
        }

-- Create a new Hermitage, does not return until the interaction
-- is completed.
new :: (Hermitage Everything ModGuts -> CoreM (Hermitage Everything ModGuts)) -> ModGuts -> CoreM ModGuts
new k modGuts = do
        modGuts' <- k (Hermitage modGuts InitialFocus initHermitEnv)
        return (getModGuts modGuts')

-- | What are the *current* module guts?
getModGuts :: Hermitage cxt a -> ModGuts
getModGuts age = ageModGuts age

-- | 'getForeground' gets the current 'blob' under consideraton.
getForeground :: Hermitage cxt a -> CoreM a
getForeground age = do
        res <- getForeground' age
        case res of
          Right [a] -> return a
          Right [] -> fail $ "no foreground matches"
          Right _  -> fail $ "multiple foreground matches"
          Left msg -> fail $ "getForeground failed, should never happend; msg = " ++ msg


-- internal version of getForeground that can fail.
getForeground' :: Hermitage cxt a -> CoreM (Either String [a])
getForeground' age = runHermitM (apply (focusTranslate (ageFocus age)) (Context (ageEnv age) (ageModGuts age)))

-- this focuses in to a sub-expresssion. It will do error checking, hence the
-- need for the the CoreM.

focusHermitage :: Zoom a x
               -> Hermitage cxt a
               -> CoreM (Either HermitMessage (Hermitage (a :< cxt) x))
focusHermitage zoom age = do
        res <- getForeground' age'
        case res of
          Right [a] -> return $ Right $ age'
          _         -> return $ Left $ UnableToFocusMessage
    where
        age' = Hermitage
                { ageModGuts    = ageModGuts age
                , ageFocus      = ageFocus age `AppendFocus` zoom
                , ageEnv = ageEnv age
                }


-- always works
unfocusHermitage :: Hermitage (a :< cxt) x -> Hermitage cxt a
unfocusHermitage age = Hermitage
        { ageModGuts    = ageModGuts age
        , ageFocus      = unappendFocus $ ageFocus age
        , ageEnv        = ageEnv age
        }


applyRewrite :: Rewrite a -> Hermitage cxt a -> CoreM (Either HermitMessage (Hermitage cxt a))
applyRewrite rr age = do
        res <- runHermitM (apply (focusRewrite (ageFocus age) rr) (Context (ageEnv age) (ageModGuts age)))
        case res of
          Right guts2 -> return (Right $ age { ageModGuts = guts2 })
          Left msg -> return (Left $ HermitMessage msg)


------------------------------------------------------------------

data HermitMessage
        = UnableToFocusMessage
        | HermitMessage String
        deriving (Show)

