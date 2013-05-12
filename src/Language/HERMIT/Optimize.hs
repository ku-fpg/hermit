{-# LANGUAGE KindSignatures, GADTs #-}
module Language.HERMIT.Optimize
    ( -- * The HERMIT Plugin
      optimize
      -- ** Running translations
    , query
    , run
      -- ** Using the shell
    , interactive
      -- ** Active modifiers
    , at
    , phase
    , after
    , before
    , allPhases
    ) where

import GhcPlugins hiding (singleton, liftIO)
import qualified GhcPlugins as GHC

import Control.Monad.Operational
import Control.Monad.State hiding (guard)

import Language.HERMIT.Core
import Language.HERMIT.External hiding (Query, Shell)
import Language.HERMIT.Kernel.Scoped
import Language.HERMIT.Kure
import Language.HERMIT.Monad
import Language.HERMIT.Plugin
import qualified Language.HERMIT.Shell.Command as Shell

import System.Console.Haskeline (defaultBehavior)

data OInst :: * -> * where
    RR       :: RewriteH Core                     -> OInst ()
    Query    :: TranslateH Core a                 -> OInst a
    Shell    :: [External] -> [CommandLineOption] -> OInst ()
    Guard    :: (PhaseInfo -> Bool) -> OM ()      -> OInst ()
    -- with some refactoring of the interpreter I'm pretty sure
    -- we can make Focus polymorphic
    Focus    :: TranslateH Core Path -> OM ()     -> OInst ()

-- using operational, but would we nice to use Neil's constrained-normal package!
type OM a = ProgramT OInst (StateT InterpState IO) a

optimize :: ([CommandLineOption] -> OM ()) -> Plugin
optimize f = hermitPlugin $ \ pi -> runOM pi . f

data InterpState = InterpState { ast :: SAST, shellHack :: Maybe ([External], [CommandLineOption]) }
type InterpM a = StateT InterpState IO a

runOM :: PhaseInfo -> OM () -> ModGuts -> CoreM ModGuts
runOM pi comp = scopedKernel $ \ kernel initSAST ->
    let env = mkHermitMEnv $ GHC.liftIO . debug
        debug (DebugTick msg) = putStrLn msg
        debug (DebugCore msg _c _e) = putStrLn $ "Core: " ++ msg

        errorAbortIO err = putStrLn err >> abortS kernel
        errorAbort = liftIO . errorAbortIO

        go :: Path -> ProgramT OInst (StateT InterpState IO) () -> InterpM ()
        go path m = do
            sast <- gets ast
            v <- viewT m
            case v of
                Return a            -> return ()
                RR rr       :>>= k  -> liftIO (applyS kernel sast (pathR path (extractR rr)) env)
                                        >>= runKureM (\sast' -> modify (\s -> s { ast = sast' }))
                                                     errorAbort >> go path (k ())
                Query tr    :>>= k  -> liftIO (queryS kernel sast (pathT path (extractT tr)) env)
                                        >>= runKureM (go path . k) errorAbort
                -- TODO: rework shell so it can return to k
                --       this will significantly simplify this code
                --       as we can just call the shell directly here
                Shell es os :>>= _k -> modify (\s -> s { shellHack = Just (es,os) })
                                       -- liftIO $ Shell.interactive os defaultBehavior es kernel sast
                                       -- calling the shell directly causes indefinite MVar problems
                                       -- because the state monad never finishes (I think)
                Guard p m   :>>= k  -> when (p pi) (go path m) >> go path (k ())
                Focus tp m  :>>= k  -> liftIO (queryS kernel sast (extractT tp) env)
                                        >>= runKureM (flip go m) errorAbort >> go path (k ())
    in do st <- execStateT (go [] comp) $ InterpState initSAST Nothing
          let sast = ast st
          maybe (liftIO (resumeS kernel sast) >>= runKureM return errorAbortIO)
                (\(es,os) -> liftIO $ Shell.interactive os defaultBehavior es kernel sast)
                (shellHack st)

interactive :: [External] -> [CommandLineOption] -> OM ()
interactive es os = singleton $ Shell es os

run :: RewriteH Core -> OM ()
run = singleton . RR

query :: TranslateH Core a -> OM a
query = singleton . Query

------------------------ target modifiers -------------------------

guard :: (PhaseInfo -> Bool) -> OM () -> OM ()
guard p = singleton . Guard p

at :: TranslateH Core Path -> OM () -> OM ()
at tp = singleton . Focus tp

phase :: Int -> OM () -> OM ()
phase n = guard ((n ==) . phaseNum)

after :: CorePass -> OM () -> OM ()
after cp = guard ((cp `elem`) . phasesDone)

before :: CorePass -> OM () -> OM ()
before cp = guard ((cp `notElem`) . phasesDone)

allPhases :: OM () -> OM ()
allPhases = guard (const True)
