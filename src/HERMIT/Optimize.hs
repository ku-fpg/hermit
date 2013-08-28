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
    , InterpState(..)
    , omToIO
    ) where

import GhcPlugins hiding (singleton, liftIO, display, (<>))
import qualified GhcPlugins as GHC

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
import HERMIT.Monad
import HERMIT.Plugin
import HERMIT.PrettyPrinter.Common
import qualified HERMIT.PrettyPrinter.Clean as Clean
import HERMIT.Shell.Command

import System.Console.Haskeline (defaultBehavior)
import System.IO (stdout)

data OInst :: * -> * where
    Shell    :: [External] -> [CommandLineOption] -> OInst ()
    Guard    :: (PhaseInfo -> Bool) -> OM ()      -> OInst ()
    Focus    :: (Injection GHC.ModGuts g, Walker HermitC g) => TranslateH g LocalPathH -> OM a -> OInst a
    RR       :: (Injection GHC.ModGuts g, Walker HermitC g) => RewriteH g                      -> OInst ()
    Query    :: (Injection GHC.ModGuts g, Walker HermitC g) => TranslateH g a                  -> OInst a

-- using operational, but would we nice to use Neil's constrained-normal package!
newtype OM a = OM (ProgramT OInst (StateT InterpState IO) a)
    deriving (Monad, MonadIO, MonadState InterpState)

optimize :: ([CommandLineOption] -> OM ()) -> Plugin
optimize f = hermitPlugin $ \ phaseInfo -> runOM phaseInfo . f

data InterpState =
    InterpState { isAST :: SAST
                , isPretty :: PrettyH CoreTC
                , isPrettyOptions :: PrettyOptions
                , isKernel :: ScopedKernel
                , isPhaseInfo :: PhaseInfo
                -- TODO: remove once shell can return
                , shellHack :: Maybe ([External], [CommandLineOption])
                }
type InterpM a = StateT InterpState IO a

runOM :: PhaseInfo -> OM () -> ModGuts -> CoreM ModGuts
runOM phaseInfo opt = scopedKernel $ \ kernel initSAST -> do
    let initState = InterpState { isAST = initSAST
                                , isPretty = Clean.ppCoreTC
                                , isPrettyOptions = def
                                , isKernel = kernel
                                , isPhaseInfo = phaseInfo
                                , shellHack = Nothing }

    (_,st) <- omToIO initState opt
    let sast = isAST st
    maybe (liftIO (resumeS kernel sast) >>= runKureM return (errorAbortIO kernel))
          (\(es,os) -> liftIO $ commandLine os defaultBehavior es kernel sast)
          (shellHack st)

errorAbortIO :: ScopedKernel -> String -> IO a
errorAbortIO kernel err = putStrLn err >> abortS kernel >> return undefined

errorAbort :: String -> InterpM a
errorAbort s = gets isKernel >>= \k -> liftIO $ errorAbortIO k s

-- TODO - better name!
omToIO :: InterpState -> OM a -> IO (a, InterpState)
omToIO initState (OM opt) = runStateT (eval opt) initState

eval :: ProgramT OInst (StateT InterpState IO) a -> InterpM a
eval comp = do
    let env = mkHermitMEnv $ GHC.liftIO . debug
        debug (DebugTick msg) = putStrLn msg
        debug (DebugCore msg _c _e) = putStrLn $ "Core: " ++ msg

    (phaseInfo, kernel) <- gets (isPhaseInfo &&& isKernel)
    v <- viewT comp
    case v of
        Return x            -> return x
        RR rr       :>>= k  -> do runAndSave $ \ sast -> applyS kernel sast rr env
                                  eval (k ())
        Query tr    :>>= k  -> do sast <- gets isAST
                                  r <- iokm2im (queryS kernel sast tr env)
                                  eval $ k r
        -- TODO: rework shell so it can return to k
        --       this will significantly simplify this code
        --       as we can just call the shell directly here
        Shell es os :>>= _k -> modify (\s -> s { shellHack = Just (es,os) }) >> return undefined
                               -- liftIO $ Shell.interactive os defaultBehavior es kernel sast
                               -- calling the shell directly causes indefinite MVar problems
                               -- because the state monad never finishes (I think)
        Guard p (OM m)  :>>= k  -> when (p phaseInfo) (eval m) >> eval (k ())
        Focus tp (OM m) :>>= k  -> do
            sast <- gets isAST
            p <- iokm2im $ queryS kernel sast tp env        -- run the pathfinding translation
            runAndSave $ beginScopeS kernel                 -- remember the current path
            runAndSave $ \s -> modPathS kernel s (<> p) env -- modify the current path
            r <- eval m                                     -- run the focused computation
            runAndSave $ endScopeS kernel                   -- endscope on it, so we go back to where we started
            eval $ k r

iokm2im :: IO (KureM a) -> InterpM a
iokm2im = liftIO >=> runKureM return errorAbort

runAndSave :: (SAST -> IO (KureM SAST)) -> InterpM ()
runAndSave m = do
    sast <- gets isAST >>= iokm2im . m
    modify $ \st -> st { isAST = sast }

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
    po <- gets isPrettyOptions
    gets isPretty >>= query . liftPrettyH po >>= liftIO . unicodeConsole stdout po

setPretty :: PrettyH CoreTC -> OM ()
setPretty pp = modify $ \s -> s { isPretty = pp }

setPrettyOptions :: PrettyOptions -> OM ()
setPrettyOptions po = modify $ \s -> s { isPrettyOptions = po }
