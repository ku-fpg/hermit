{-# LANGUAGE KindSignatures, GADTs, TupleSections #-}

module Language.HERMIT.Command
        ( Command(..)
        , runCommands
        ) where

import GhcPlugins
import Control.Monad

import Language.KURE

import Language.HERMIT.HermitKure
import Language.HERMIT.HermitEnv
import Language.HERMIT.HermitMonad

-- | 'Command' is what you send to the HERMIT kernel.
data Command :: * where
   Exit          ::                             Command
   Message       :: String                   -> Command
   Apply         :: RewriteH Core            -> Command
   Query         :: TranslateH Core String   -> Command
   PushFocus     :: LensH Core Core          -> Command
   PopFocus      ::                             Command
   SuperPopFocus ::                             Command

instance Show Command where
   show (Exit)          = "Exit"
   show (Apply _)       = "Apply"
   show (Query _)       = "Query"
   show (PushFocus _)   = "PushFocus"
   show (PopFocus)      = "PopFocus"
   show (SuperPopFocus) = "SuperPopFocus"
   show (Message _)     = "Message"


type Pop = (HermitEnv,(Core -> HermitM Core))

runCommands :: (HermitEnv -> Core -> IO Command)  -- waiting for commands
            -> (String -> IO ())                  -- where to send output
            -> ModGuts -> CoreM ModGuts
runCommands getCommand output modGuts = do
        ModGutsCore modGuts' <- loop [] c0 a0
        return modGuts'
  where
    c0 :: HermitEnv
    c0 = initHermitEnv

    a0 :: Core
    a0 = ModGutsCore modGuts

    loop :: [Pop] -> HermitEnv -> Core -> CoreM Core
    loop pops c a = do rep <- liftIO (getCommand c a)
                       case rep of
                         PushFocus l   -> runHermitMR (\ ((c',b),k) -> loop ((c,k):pops) c' b) printAndLoop (apply l c a)
                         PopFocus      -> popAndLoop pops
                         SuperPopFocus -> popAll pops >>= loop [] c0
                         Apply rr      -> runHermitMR (loop pops c) printAndLoop (apply rr c a)
                         Query tt      -> runHermitMR printAndLoop printAndLoop (apply tt c a)
                         Message msg   -> printAndLoop msg
                         Exit          -> popAll pops

      where
        popAndLoop :: [Pop] -> CoreM Core
        popAndLoop []           = printAndLoop "Nothing to pop, already at root."
        popAndLoop ((c',k):cks) = runHermitMR (loop cks c') printAndLoop (k a)

        popAll :: [Pop] -> CoreM Core
        popAll []  = return a
        popAll cks = runHermitMR return
                                 (\ msg -> printMsg msg >> return a0) -- if popping fails revert to initial value
                                 (foldM (flip ($)) a (map snd cks))

        printMsg :: String -> CoreM ()
        printMsg = liftIO . output . show

        printAndLoop :: String -> CoreM Core
        printAndLoop s = printMsg s >> loop pops c a
