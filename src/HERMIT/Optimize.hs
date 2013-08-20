{-# LANGUAGE KindSignatures, GADTs, FlexibleContexts #-}
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
    ) where

import GhcPlugins hiding (singleton, liftIO, display)
import qualified GhcPlugins as GHC

import Control.Monad.Operational
import Control.Monad.State hiding (guard)

import Data.Default

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
    -- with some refactoring of the interpreter I'm pretty sure
    -- we can make Focus polymorphic
    Focus    :: (Injection GHC.ModGuts g, Walker HermitC g) => TranslateH g PathH -> OM () -> OInst ()
    RR       :: (Injection GHC.ModGuts g, Walker HermitC g) => RewriteH g                  -> OInst ()
    Query    :: (Injection GHC.ModGuts g, Walker HermitC g) => TranslateH g a              -> OInst a

-- using operational, but would we nice to use Neil's constrained-normal package!
type OM a = ProgramT OInst (StateT InterpState IO) a

optimize :: ([CommandLineOption] -> OM ()) -> Plugin
optimize f = hermitPlugin $ \ phaseInfo -> runOM phaseInfo . f

data InterpState =
    InterpState { isAST :: SAST
                , isPretty :: PrettyH CoreTC
                , isPrettyOptions :: PrettyOptions
                -- TODO: remove once shell can return
                , shellHack :: Maybe ([External], [CommandLineOption])
                }
type InterpM a = StateT InterpState IO a

runOM :: PhaseInfo -> OM () -> ModGuts -> CoreM ModGuts
runOM phaseInfo opt = scopedKernel $ \ kernel initSAST ->
    let env = mkHermitMEnv $ GHC.liftIO . debug
        debug (DebugTick msg) = putStrLn msg
        debug (DebugCore msg _c _e) = putStrLn $ "Core: " ++ msg

        errorAbortIO err = putStrLn err >> abortS kernel
        errorAbort = liftIO . errorAbortIO

        initState = InterpState initSAST Clean.ppCoreTC def Nothing

        eval :: PathH -> ProgramT OInst (StateT InterpState IO) () -> InterpM ()
        eval path comp = do
            sast <- gets isAST
            v <- viewT comp
            case v of
                Return _            -> return ()
                RR rr       :>>= k  -> liftIO (applyS kernel sast (pathR path rr) env)
                                        >>= runKureM (\sast' -> modify (\s -> s { isAST = sast' }))
                                                     errorAbort >> eval path (k ())
                Query tr    :>>= k  -> liftIO (queryS kernel sast (pathT path tr) env)
                                        >>= runKureM (eval path . k) errorAbort
                -- TODO: rework shell so it can return to k
                --       this will significantly simplify this code
                --       as we can just call the shell directly here
                Shell es os :>>= _k -> modify (\s -> s { shellHack = Just (es,os) })
                                       -- liftIO $ Shell.interactive os defaultBehavior es kernel sast
                                       -- calling the shell directly causes indefinite MVar problems
                                       -- because the state monad never finishes (I think)
                Guard p m   :>>= k  -> when (p phaseInfo) (eval path m) >> eval path (k ())
                Focus tp m  :>>= k  -> liftIO (queryS kernel sast tp env)
                                        >>= runKureM (flip eval m) errorAbort >> eval path (k ())

    in do st <- execStateT (eval [] opt) initState
          let sast = isAST st
          maybe (liftIO (resumeS kernel sast) >>= runKureM return errorAbortIO)
                (\(es,os) -> liftIO $ commandLine os defaultBehavior es kernel sast)
                (shellHack st)

interactive :: [External] -> [CommandLineOption] -> OM ()
interactive es os = singleton $ Shell (externals ++ es) os

run :: RewriteH Core -> OM ()
run = singleton . RR

query :: (Injection GHC.ModGuts g, Walker HermitC g) => TranslateH g a -> OM a
query = singleton . Query

----------------------------- guards ------------------------------

guard :: (PhaseInfo -> Bool) -> OM () -> OM ()
guard p = singleton . Guard p

at :: TranslateH Core PathH -> OM () -> OM ()
at tp = singleton . Focus tp

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
