{-# LANGUAGE FlexibleContexts, RankNTypes, GADTs, ImpredicativeTypes, GeneralizedNewtypeDeriving #-}
module Language.HERMIT.Optimize
       ( -- * The HERMIT Plugin
         optimize
       , at
       , run
       , interactive
)  where

import GhcPlugins

import Control.Applicative
import Control.Monad.Error
import Control.Monad.State

import Language.HERMIT.Core
import Language.HERMIT.External
import Language.HERMIT.Kernel.Scoped
import Language.HERMIT.Kure
import Language.HERMIT.Monad
import Language.HERMIT.Plugin
import qualified Language.HERMIT.Shell.Command as Shell

import System.Console.Haskeline (defaultBehavior)

newtype OptimizeM a = OptimizeM { runOptimizeM :: ErrorT String (StateT OptState IO) a }
    deriving (Monad, MonadIO, Functor, MonadState OptState, MonadError String)

data OptState = OptState { kernel :: ScopedKernel
                         , sast :: SAST
                         , mEnv :: HermitMEnv }

run :: Injection a Core => RewriteH a -> OptimizeM ()
run rr = do
    liftIO $ putStrLn "running"
    k <- gets kernel
    ast <- gets sast
    env <- gets mEnv

    kres <- liftIO (applyS k ast (extractR (promoteR rr :: RewriteH Core)) env)
    runKureM (\ast' -> modify (\s -> s { sast = ast' })) throwError kres

at :: TranslateH Core Path -> OptimizeM () -> OptimizeM ()
at = undefined
-- at t m =

--interactive :: [FilePath] -> Behavior -> ScopedKernel -> SAST -> IO ()
interactive :: [External] -> OptimizeM ()
interactive exts = do
    k <- gets kernel
    ast <- gets sast

    liftIO $ Shell.interactive [] defaultBehavior exts k ast

--display :: OptimizeM ()
--display = OptimizeM [corePrettyH def

runO :: OptimizeM () -> ScopedKernel -> SAST -> IO ()
runO opt skernel ast = do
    let env = mkHermitMEnv $ \ _ -> return ()
        initState = OptState skernel ast env
        errAction err = putStrLn err >> abortS skernel

    (res, st) <- flip runStateT initState $ runErrorT $ runOptimizeM opt

    either errAction (\() -> resumeS skernel (sast st) >>= runKureM return errAction) res

optimize :: OptimizeM () -> Plugin
optimize os = hermitPlugin $ \ opts -> scopedKernel $ runO os

{-
-- | Given a list of 'CommandLineOption's, produce the 'ModGuts' to 'ModGuts' function required to build a plugin.
type HermitPass = [CommandLineOption] -> ModGuts -> CoreM ModGuts

data Options = Options { pass :: Int }

instance Default Options where
    def = Options { pass = 0 }

parse :: [String] -> Options -> Options
parse (('-':'p':n):rest) o | all isDigit n = parse rest $ o { pass = read n }
parse (_:rest) o = parse rest o -- unknown option
parse [] o       = o

-- | Build a hermit plugin. This mainly handles the per-module options.
hermitPlugin :: HermitPass -> Plugin
hermitPlugin hp = defaultPlugin { installCoreToDos = install }
    where
        install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
        install opts todos = do
            reinitializeGlobals

            -- This is a bit of a hack; otherwise we lose what we've not seen
            liftIO $ hSetBuffering stdout NoBuffering

            dynFlags <- getDynFlags

            let (m_opts, h_opts) = partition (isInfixOf ":") opts
                hermit_opts = parse h_opts def
                myPass = CoreDoPluginPass "HERMIT" $ modFilter dynFlags hp m_opts
                -- at front, for now
                allPasses = insertAt (pass hermit_opts) myPass todos

            return allPasses

-- | Determine whether to act on this module, choose plugin pass.
modFilter :: DynFlags -> HermitPass -> HermitPass
modFilter dynFlags hp opts guts | null modOpts && not (null opts) = return guts -- don't process this module
                                | otherwise                       = hp modOpts guts
    where modOpts = filterOpts dynFlags opts guts

-- | Filter options to those pertaining to this module, stripping module prefix.
filterOpts :: DynFlags -> [CommandLineOption] -> ModGuts -> [CommandLineOption]
filterOpts dynFlags opts guts = [ drop len nm | nm <- opts, modName `isPrefixOf` nm ]
    where modName = showPpr dynFlags $ mg_module guts
          len = length modName + 1 -- for the colon

insertAt :: Int -> a -> [a] -> [a]
insertAt n x xs = pre ++ (x : suf)
    where (pre,suf) = splitAt n xs
-}
