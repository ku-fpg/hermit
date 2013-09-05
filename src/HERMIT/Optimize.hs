{-# LANGUAGE KindSignatures, GADTs, FlexibleContexts, GeneralizedNewtypeDeriving #-}
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
import Control.Monad.Operational
import Control.Monad.State hiding (guard)

import Data.Default
import Data.Monoid

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
    let initState = CommandLineState
                       { cl_cursor         = initSAST
                       , cl_pretty         = Clean.ppCoreTC
                       , cl_pretty_opts    = def { po_width = 80 }
                       , cl_render         = unicodeConsole
                       , cl_height         = 30
                       , cl_nav            = False
                       , cl_running_script = False
                       , cl_tick          = error "cl_tick" -- TODO: var
                       , cl_corelint      = True
                       , cl_failhard      = True
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
    either (\ err -> putStrLn err >> abortS kernel) (\ _ -> resumeS kernel $ cl_cursor st) r

-- TODO - better name!
omToIO :: CommandLineState -> PhaseInfo -> OM a -> IO (Either String a, CommandLineState)
omToIO initState phaseInfo (OM opt) = runCLMToIO initState (eval phaseInfo opt)

eval :: PhaseInfo -> ProgramT OInst (CLM IO) a -> CLM IO a
eval phaseInfo comp = do
    let env = mkHermitMEnv $ GHC.liftIO . debug
        debug (DebugTick msg) = putStrLn msg
        debug (DebugCore msg _c _e) = putStrLn $ "Core: " ++ msg

    kernel <- gets cl_kernel
    v <- viewT comp
    case v of
        Return x            -> return x
        RR rr       :>>= k  -> do runAndSave $ applyS kernel rr env
                                  eval phaseInfo $ k ()
        Query tr    :>>= k  -> do sast <- gets cl_cursor
                                  r <- queryS kernel tr env sast
                                  eval phaseInfo $ k r
        -- TODO: rework shell so it can return to k
        --       this will significantly simplify this code
        --       as we can just call the shell directly here
        Shell es os :>>= _k -> gets cl_cursor >>= liftIO . commandLine os defaultBehavior es kernel >> return undefined
        Guard p (OM m)  :>>= k  -> when (p phaseInfo) (eval phaseInfo m) >> eval phaseInfo (k ())
        Focus tp (OM m) :>>= k  -> do
            sast <- gets cl_cursor
            p <- queryS kernel tp env sast          -- run the pathfinding translation
            runAndSave $ beginScopeS kernel         -- remember the current path
            runAndSave $ modPathS kernel (<> p) env -- modify the current path
            r <- eval phaseInfo m                   -- run the focused computation
            runAndSave $ endScopeS kernel           -- endscope on it, so we go back to where we started
            eval phaseInfo $ k r

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
