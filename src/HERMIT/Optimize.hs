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
    , allPhases
    , firstPhase
    , lastPhase
      -- ** Types
    , OM
    , omToIO
    ) where

import Control.Arrow
import Control.Concurrent.STM
import Control.Monad.Error hiding (guard)
import Control.Monad.Operational
import Control.Monad.State hiding (guard)

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
import HERMIT.Plugin
import HERMIT.PrettyPrinter.Common
import qualified HERMIT.PrettyPrinter.Clean as Clean
import HERMIT.Shell.Command
import HERMIT.Shell.Types

import System.Console.Haskeline (defaultBehavior)
import System.IO (stdout)

data OInst :: * -> * where
    Shell    :: [External] -> [CommandLineOption] -> OInst ()
    Guard    :: (PhaseInfo -> Bool) -> OM ()      -> OInst ()
    Focus    :: (Injection ModGuts g, Walker HermitC g) => TranslateH g LocalPathH -> OM a -> OInst a
    RR       :: (Injection ModGuts g, Walker HermitC g) => RewriteH g                      -> OInst ()
    Query    :: (Injection ModGuts g, Walker HermitC g) => TranslateH g a                  -> OInst a

newtype OM a = OM (ProgramT OInst (CLM IO) a)
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
                       , cl_corelint      = True
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
omToIO initState phaseInfo (OM opt) = runCLM initState (eval phaseInfo opt)

eval :: PhaseInfo -> ProgramT OInst (CLM IO) a -> CLM IO a
eval phaseInfo comp = do
    (kernel, env) <- gets $ cl_kernel &&& cl_kernel_env
    v <- viewT comp
    case v of
        Return x            -> return x
        RR rr       :>>= k  -> do runAndSave $ applyS kernel rr env
                                  eval phaseInfo $ k ()
        Query tr    :>>= k  -> do sast <- gets cl_cursor
                                  r <- queryS kernel tr env sast
                                  eval phaseInfo $ k r
        Shell es os :>>= k -> catchContinue (commandLine os defaultBehavior es) >>= eval phaseInfo . k
        Guard p (OM m)  :>>= k  -> when (p phaseInfo) (eval phaseInfo m) >> eval phaseInfo (k ())
        Focus tp (OM m) :>>= k  -> do
            sast <- gets cl_cursor
            p <- queryS kernel tp env sast          -- run the pathfinding translation
            runAndSave $ beginScopeS kernel         -- remember the current path
            runAndSave $ modPathS kernel (<> p) env -- modify the current path
            r <- eval phaseInfo m                   -- run the focused computation
            runAndSave $ endScopeS kernel           -- endscope on it, so we go back to where we started
            eval phaseInfo $ k r

catchContinue :: Monad m => CLM m () -> CLM m ()
catchContinue m = catchError m (\case CLContinue st -> put st
                                      other -> throwError other)

runAndSave :: (SAST -> CLM IO SAST) -> CLM IO ()
runAndSave f = do
    sast <- gets cl_cursor >>= f
    modify $ \st -> st { cl_cursor = sast }

interactive :: [External] -> [CommandLineOption] -> OM ()
interactive es os = OM . singleton $ Shell (externals ++ es) os

run :: RewriteH Core -> OM ()
run = OM . singleton . RR

query :: (Injection GHC.ModGuts g, Walker HermitC g) => TranslateH g a -> OM a
query = OM . singleton . Query

----------------------------- guards ------------------------------

guard :: (PhaseInfo -> Bool) -> OM () -> OM ()
guard p = OM . singleton . Guard p

at :: TranslateH Core LocalPathH -> OM a -> OM a
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

allPhases :: OM () -> OM ()
allPhases = guard (const True)

firstPhase :: OM () -> OM ()
firstPhase = guard (null . phasesDone)

lastPhase :: OM () -> OM ()
lastPhase = guard (null . phasesLeft)

----------------------------- other ------------------------------

display :: OM ()
display = do
    (po,r) <- OM $ gets $ cl_pretty_opts &&& cl_render
    OM (gets cl_pretty) >>= query . liftPrettyH po >>= liftIO . r stdout po . Right

setPretty :: PrettyH CoreTC -> OM ()
setPretty pp = OM $ modify $ \s -> s { cl_pretty = pp }

setPrettyOptions :: PrettyOptions -> OM ()
setPrettyOptions po = OM $ modify $ \s -> s { cl_pretty_opts = po }
