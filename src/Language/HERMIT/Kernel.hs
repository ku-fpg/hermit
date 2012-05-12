{-# LANGUAGE KindSignatures, GADTs #-}

module Language.HERMIT.Kernel ( 
          
          KernelCommand(..)
        , KernelOutput(..)  
        , runCommands
          
) where

import GhcPlugins
import Control.Monad

import Language.KURE

import Language.HERMIT.HermitKure
import Language.HERMIT.HermitEnv
import Language.HERMIT.HermitMonad

-- | 'KernelCommand' is what you send to the HERMIT kernel.
data KernelCommand :: * where
   Exit          ::                             KernelCommand
   Message       :: String                   -> KernelCommand
   Apply         :: RewriteH Core            -> KernelCommand
   Query         :: TranslateH Core String   -> KernelCommand
   PushFocus     :: LensH Core Core          -> KernelCommand
   PopFocus      ::                             KernelCommand
   SuperPopFocus ::                             KernelCommand

instance Show KernelCommand where
   show Exit           = "Exit"
   show (Apply _)      = "Apply"
   show (Query _)      = "Query"
   show (PushFocus _)  = "PushFocus"
   show PopFocus       = "PopFocus"
   show SuperPopFocus  = "SuperPopFocus"
   show (Message msg)  = "Message: " ++ msg

-- | 'KernalOutput' is what the HERMIT kernel sends back.
data KernelOutput :: * where
   ErrorMsg    :: String            -> KernelOutput
   QueryResult :: String            -> KernelOutput
   FocusChange :: HermitEnv -> Core -> KernelOutput
   CoreChange  :: Core              -> KernelOutput

instance Show KernelOutput where
   show (ErrorMsg msg)    = "Error message: " ++ msg
   show (QueryResult msg) = "Query result: " ++ msg
   show (FocusChange _ _) = "Focus change"
   show (CoreChange _)    = "Core change"

type Pop = (HermitEnv, Core -> HermitM Core)

runCommands :: CoreM KernelCommand -> (KernelOutput -> CoreM ()) -> ModGuts -> CoreM ModGuts
runCommands getCommand output modGuts = do ModGutsCore modGuts' <- newFocus [] c0 a0
                                           return modGuts'
  where
    c0 :: HermitEnv
    c0 = initHermitEnv

    a0 :: Core
    a0 = ModGutsCore modGuts

    queryOut :: String -> CoreM ()
    queryOut = output . QueryResult
        
    errOut :: String -> CoreM ()
    errOut =  output . ErrorMsg

    newFocus :: [Pop] -> HermitEnv -> Core -> CoreM Core
    newFocus pops c a = (output $ FocusChange c a) >> loop pops c a

    loop :: [Pop] -> HermitEnv -> Core -> CoreM Core
    loop pops c a = do cmd <- getCommand
                       case cmd of
                         Apply rr      -> runHermitMR coreChange errOutCont (apply rr c a)
                         Query tt      -> runHermitMR queryOut errOut (apply tt c a) >> continue
                         PushFocus l   -> runHermitMR (\ ((c',b),k) -> newFocus ((c,k):pops) c' b) errOutCont (apply l c a)
                         PopFocus      -> case pops of
                                            []           -> errOutCont "Nothing to pop, already at root."
                                            ((c',k):cks) -> runHermitMR (newFocus cks c') errOutCont (k a)
                         SuperPopFocus -> popAll pops >>= newFocus [] c0
                         Exit          -> popAll pops
                         Message msg   -> continue -- currently messages are ignores

      where
        continue :: CoreM Core
        continue = loop pops c a
        
        errOutCont :: String -> CoreM Core
        errOutCont msg = errOut msg >> continue

        coreChange :: Core -> CoreM Core
        coreChange a' = output (CoreChange a') >> loop pops c a'
        
        popAll :: [Pop] -> CoreM Core
        popAll []  = return a
        popAll cks = runHermitMR return
                                 ( \ msg -> errOut (msg ++ " Reverting to initial state.") >> return a0)
                                 (foldM (flip ($)) a (map snd cks))