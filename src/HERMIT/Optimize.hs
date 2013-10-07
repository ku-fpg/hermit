{-# LANGUAGE KindSignatures, GADTs, FlexibleContexts, GeneralizedNewtypeDeriving, LambdaCase #-}
module HERMIT.Optimize
    ( -- * The HERMIT Plugin
      optimize
      -- ** Running translations
    , query
    , run
      -- ** Using the shell
    , interactive
    , display
    , setPretty
    , setPrettyOptions
      -- ** Active modifiers
    , at
    , phase
    , after
    , before
    , until
    , allPhases
    , firstPhase
    , lastPhase
      -- ** Knobs and Dials
    , getPhaseInfo
    , modifyCLS
      -- ** Types
    , OM
    , omToIO
    ) where

import Control.Arrow
import Control.Concurrent.STM
import Control.Monad.Error hiding (guard)
import Control.Monad.Operational
import Control.Monad.State hiding (guard)
import Control.Monad.Reader hiding (guard)

import Data.Default
import Data.Monoid
import qualified Data.Map as M

import HERMIT.Dictionary
import HERMIT.External hiding (Query, Shell)
import HERMIT.Kernel.Scoped
import HERMIT.Context
import HERMIT.Kure
import HERMIT.GHC hiding (singleton, liftIO, display, (<>))
import qualified HERMIT.GHC as GHC
import HERMIT.Monad
import HERMIT.Plugin
import HERMIT.PrettyPrinter.Common
import qualified HERMIT.PrettyPrinter.Clean as Clean
import HERMIT.Shell.Command
import HERMIT.Shell.Types

import Prelude hiding (until)

import System.Console.Haskeline (defaultBehavior)

data OInst :: * -> * where
    Shell    :: [External] -> [CommandLineOption] -> OInst ()
    Guard    :: (PhaseInfo -> Bool) -> OM ()      -> OInst ()
    Focus    :: (Injection ModGuts g, Walker HermitC g) => TranslateH g LocalPathH -> OM a -> OInst a
    RR       :: (Injection ModGuts g, Walker HermitC g) => RewriteH g                      -> OInst ()
    Query    :: (Injection ModGuts g, Walker HermitC g) => TranslateH g a                  -> OInst a

newtype OM a = OM (ProgramT OInst (ReaderT PhaseInfo (CLM IO)) a)
    deriving (Monad, MonadIO)

optimize :: ([CommandLineOption] -> OM ()) -> Plugin
optimize f = hermitPlugin $ \ phaseInfo -> runOM phaseInfo . f

runOM :: PhaseInfo -> OM () -> ModGuts -> CoreM ModGuts
runOM phaseInfo opt = scopedKernel $ \ kernel initSAST -> do
    tick <- liftIO $ atomically $ newTVar M.empty
    let initState = CommandLineState
                       { cl_cursor         = initSAST
                       , cl_pretty         = Clean.ppCoreTC
                       , cl_pretty_opts    = def { po_width = 80 }
                       , cl_render         = unicodeConsole
                       , cl_height         = 30
                       , cl_nav            = False
                       , cl_running_script = False
                       , cl_tick          = tick
                       , cl_corelint      = False
                       , cl_failhard      = False
                       , cl_window        = mempty
                       , cl_dict          = error "cl_dict" -- TODO
                       , cl_scripts       = []
                       , cl_kernel        = kernel
                       , cl_initSAST      = initSAST
                       , cl_version       = VersionStore
                                              { vs_graph = []
                                              , vs_tags  = []
                                              }
                       }

    (r,st) <- omToIO initState phaseInfo opt
    either (\case CLAbort         -> abortS kernel
                  CLResume   sast -> resumeS kernel sast
                  CLContinue _    -> putStrLn "Uncaught CLContinue! Aborting..." >> abortS kernel
                  CLError    err  -> putStrLn err >> abortS kernel)
           (\ _ -> resumeS kernel $ cl_cursor st) r

-- TODO - better name!
omToIO :: CommandLineState -> PhaseInfo -> OM a -> IO (Either CLException a, CommandLineState)
omToIO initState phaseInfo (OM opt) = runCLM initState (runReaderT (eval opt) phaseInfo)

eval :: ProgramT OInst (ReaderT PhaseInfo (CLM IO)) a -> ReaderT PhaseInfo (CLM IO) a
eval comp = do
    (kernel, env) <- gets $ cl_kernel &&& cl_kernel_env
    v <- viewT comp
    case v of
        Return x            -> return x
        RR rr       :>>= k  -> lift (runS (applyS kernel rr env)) >>= eval . k
        Query tr    :>>= k  -> lift (runK (queryS kernel tr env)) >>= eval . k
        Shell es os :>>= k -> do
            lift $ do
                -- We want to discard the current focus, open the shell at
                -- the top level, then restore the current focus.
                paths <- resetScoping env
                catchContinue (commandLine os defaultBehavior es)
                _ <- resetScoping env
                restoreScoping env paths
            eval $ k ()
        Guard p (OM m)  :>>= k  -> ask >>= \ phaseInfo -> when (p phaseInfo) (eval m) >>= eval . k
        Focus tp (OM m) :>>= k  -> do
            lift $ do
                sast <- gets cl_cursor
                p <- queryS kernel tp env sast    -- run the pathfinding translation
                runS $ beginScopeS kernel         -- remember the current path
                runS $ modPathS kernel (<> p) env -- modify the current path
            r <- eval m             -- run the focused computation
            lift $ runS $ endScopeS kernel           -- endscope on it, so we go back to where we started
            eval $ k r

------------------------- Shell-related helpers --------------------------------------

catchContinue :: Monad m => CLM m () -> CLM m ()
catchContinue m = catchError m (\case CLContinue st -> put st
                                      other -> throwError other)

resetScoping :: HermitMEnv -> CLM IO [PathH]
resetScoping env = do
    kernel <- gets cl_kernel
    paths <- runK $ pathS kernel
    replicateM_ (length paths - 1) $ runS $ endScopeS kernel
    -- modPathS commonly fails here because the path is unchanged, so throw away failures
    catchM (runS $ modPathS kernel (const mempty) env) (const (return ()))
    return paths

restoreScoping :: HermitMEnv -> [PathH] -> CLM IO ()
restoreScoping _   []    = return ()
restoreScoping env (h:t) = do
    kernel <- gets cl_kernel

    let go p []      = restore p
        go p (p':ps) = restore p >> runS (beginScopeS kernel) >> go p' ps

        -- modPathS commonly fails here because the path is unchanged, so throw away failures
        restore p = catchM (runS $ modPathS kernel (<> pathToSnocPath p) env)
                           (const (return ()))

    go h t

-- | Run a kernel function on the current SAST
runK :: (SAST -> CLM IO a) -> CLM IO a
runK f = gets cl_cursor >>= f

-- | Run a kernel function on the current SAST and update cl_cursor
runS :: (SAST -> CLM IO SAST) -> CLM IO ()
runS f = do
    sast <- runK f
    modify $ \st -> st { cl_cursor = sast }

interactive :: [External] -> [CommandLineOption] -> OM ()
interactive es os = OM . singleton $ Shell (externals ++ es) os

run :: RewriteH CoreTC -> OM ()
run = OM . singleton . RR

query :: (Injection GHC.ModGuts g, Walker HermitC g) => TranslateH g a -> OM a
query = OM . singleton . Query

----------------------------- guards ------------------------------

guard :: (PhaseInfo -> Bool) -> OM () -> OM ()
guard p = OM . singleton . Guard p

at :: TranslateH CoreTC LocalPathH -> OM a -> OM a
at tp = OM . singleton . Focus tp

phase :: Int -> OM () -> OM ()
phase n = guard ((n ==) . phaseNum)

after :: CorePass -> OM () -> OM ()
after cp = guard (\phaseInfo -> case phasesDone phaseInfo of
                            [] -> False
                            xs -> last xs == cp)

before :: CorePass -> OM () -> OM ()
before cp = guard (\phaseInfo -> case phasesLeft phaseInfo of
                            (x:_) | cp == x -> True
                            _               -> False)

until :: CorePass -> OM () -> OM ()
until cp = guard ((cp `elem`) . phasesLeft)

allPhases :: OM () -> OM ()
allPhases = guard (const True)

firstPhase :: OM () -> OM ()
firstPhase = guard (null . phasesDone)

lastPhase :: OM () -> OM ()
lastPhase = guard (null . phasesLeft)

----------------------------- other ------------------------------

getPhaseInfo :: OM PhaseInfo
getPhaseInfo = OM $ lift ask

display :: OM ()
display = OM $ lift $ lift $ performQuery Display

modifyCLS :: (CommandLineState -> CommandLineState) -> OM ()
modifyCLS = OM . modify

setPretty :: PrettyH CoreTC -> OM ()
setPretty pp = modifyCLS $ \s -> s { cl_pretty = pp }

setPrettyOptions :: PrettyOptions -> OM ()
setPrettyOptions po = modifyCLS $ \s -> s { cl_pretty_opts = po }
