{-# LANGUAGE KindSignatures, GADTs, RankNTypes, ScopedTypeVariables #-}

module Language.HERMIT.Kernel (

          KernelCommand(..)
        , KernelOutput(..)
        , runCommands

        , hermitKernel
        , Kernel(..)
        , AST

) where

import GhcPlugins
import Control.Monad

import Language.KURE

import Language.HERMIT.HermitKure
import Language.HERMIT.HermitEnv
import Language.HERMIT.HermitMonad

import qualified Data.Map as M
import Control.Concurrent
import Control.Concurrent.MVar

data Kernel = Kernel
        { quitK   ::            AST                      -> IO ()
        , applyK  ::            AST -> RewriteH Core     -> IO AST
        , queryK  :: forall a . AST -> TranslateH Core a -> IO a
        , deleteK ::            AST                      -> IO ()
        , listK   ::                                        IO [AST]
        }

-- a name of a syntax tree
newtype AST = AST Int
        deriving (Eq, Ord, Show)

data Msg s r = forall a . Req (s -> CoreM (a,s)) (MVar (Either String a))
             | Done (s -> CoreM r)

-- | 'hermitKernel' is a repository for our syntax trees.
-- For now, operations are sequential, but later
-- it will be possible to have two applyK's running in parallel.
--
-- The callback is only every called once.
hermitKernel :: (Kernel -> AST -> IO ())
             -> ModGuts -> CoreM ModGuts
hermitKernel callback modGuts = do

        let hEnv0 = initHermitEnv

        msg :: MVar (Msg (M.Map AST ModGuts) ModGuts) <- liftIO newEmptyMVar

        syntax_names :: MVar AST <- liftIO newEmptyMVar

        liftIO $ forkIO $
                let loop n = do
                        putMVar syntax_names (AST n)
                        loop (succ n)
                 in loop 0

        let sendDone = putMVar msg . Done

        let sendReq :: (M.Map AST ModGuts -> CoreM (a,M.Map AST ModGuts)) -> IO a
            sendReq fn = do
                rep <- newEmptyMVar
                putMVar msg (Req fn rep)
                res <- takeMVar rep
                case res of
                  Left msg -> fail msg
                  Right ans -> return ans

        let find :: (Monad m) => AST -> M.Map AST ModGuts -> (ModGuts -> m a) -> m a
            find name env k = case M.lookup name env of
              Nothing -> fail $ "can not find syntax tree : " ++ show name
              Just core -> k core

        let kernel = Kernel
                { quitK = \ name -> sendDone $ \ env -> find name env $ \ core -> return core
                , applyK = \ name rr -> sendReq $ \ env -> find name env $ \ core ->
                             runHermitMR
                                  (\ core' -> do
                                      syn' <- liftIO $ takeMVar syntax_names
                                      return (syn',M.insert syn' core' env))
                                  (\ msg -> fail msg)
                                  (apply (extractR rr) hEnv0 core)
                , queryK = \ name q -> sendReq $ \ env -> find name env $ \ core ->
                             runHermitMR
                                  (\ reply -> return (reply,env))
                                  (\ msg -> fail msg)
                                  (apply (extractT q) hEnv0 core)
                , deleteK = \ name -> sendReq $ \ env -> find name env $ \ _ ->
                             return ((), M.delete name env)
                , listK = sendReq $ \ env -> return (M.keys env,env)
                }

        -- We always start with syntax blob 0
        syn <- liftIO $ takeMVar syntax_names

        let loop st = do
                m <- liftIO $ takeMVar msg
                case m of
                  Req fn rep -> do
                          (a,st') <- fn st      -- TODO: catch a failure
                          liftIO $ putMVar rep (Right a)
                          loop st
                  Done fn -> fn st

        pid <- liftIO $ forkIO $ callback kernel syn

        modGuts' <- loop (M.singleton syn modGuts)

        -- (Kill the pid'd thread? do we need to?)

        return modGuts'


-- | 'KernelCommand' is what you send to the HERMIT kernel.
data KernelCommand :: * where
   Exit          ::                             KernelCommand
   Status        ::                             KernelCommand
   Message       :: String                   -> KernelCommand
   Apply         :: RewriteH Core            -> KernelCommand
   Query         :: TranslateH Core String   -> KernelCommand
   PushFocus     :: LensH Core Core          -> KernelCommand
   PopFocus      ::                             KernelCommand
   SuperPopFocus ::                             KernelCommand

instance Show KernelCommand where
   show Exit           = "Exit"
   show Status         = "Status"
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
                         Status        -> newFocus pops c a
                         Message _     -> continue -- currently messages are ignored

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