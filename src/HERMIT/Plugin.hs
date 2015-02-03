{-# LANGUAGE KindSignatures, GADTs, FlexibleContexts, GeneralizedNewtypeDeriving, LambdaCase #-}
module HERMIT.Plugin
    ( -- * The HERMIT Plugin
      hermitPlugin
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
    , pass
    , after
    , before
    , until
    , allPasses
    , firstPass
    , lastPass
      -- ** Knobs and Dials
    , getPassInfo
    , modifyCLS
      -- ** Types
    , defPS
    , HPM
    , hpmToIO
    ) where

import Control.Applicative
import Control.Arrow
import Control.Concurrent.STM
import Control.Monad (replicateM_, when)
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Operational
import Control.Monad.State (gets, modify)
import Control.Monad.Trans.Class (MonadTrans(..))

import Data.Monoid
import qualified Data.Map as M

import HERMIT.Dictionary
import HERMIT.External hiding (Query, Shell)
import HERMIT.Kernel (KernelEnv)
import HERMIT.Kernel.Scoped
import HERMIT.Context
import HERMIT.Kure
import HERMIT.GHC hiding (singleton, liftIO, display, (<>))
import qualified HERMIT.GHC as GHC

import HERMIT.Plugin.Builder
import qualified HERMIT.Plugin.Display as Display
import HERMIT.Plugin.Renderer
import HERMIT.Plugin.Types

import HERMIT.PrettyPrinter.Common
import qualified HERMIT.PrettyPrinter.Clean as Clean
import HERMIT.Shell.Command
import HERMIT.Shell.Types (clm)

import Prelude hiding (until)

hermitPlugin :: ([CommandLineOption] -> HPM ()) -> Plugin
hermitPlugin f = buildPlugin $ \ passInfo -> runHPM passInfo . f

defPS :: SAST -> ScopedKernel -> PassInfo -> IO PluginState
defPS initSAST kernel passInfo = do
    emptyTick <- liftIO $ atomically $ newTVar M.empty
    return $ PluginState
                { ps_cursor         = initSAST
                , ps_pretty         = Clean.pretty
                , ps_render         = unicodeConsole
                , ps_tick           = emptyTick
                , ps_corelint       = False
                , ps_diffonly       = False
                , ps_failhard       = False
                , ps_kernel         = kernel
                , ps_pass           = passInfo
                }

data HPMInst :: * -> * where
    Shell    :: [External] -> [CommandLineOption] -> HPMInst ()
    Guard    :: (PassInfo -> Bool) -> HPM ()     -> HPMInst ()
    Focus    :: (Injection ModGuts g, Walker HermitC g) => TransformH g LocalPathH -> HPM a -> HPMInst a
    RR       :: (Injection ModGuts g, Walker HermitC g) => RewriteH g                       -> HPMInst ()
    Query    :: (Injection ModGuts g, Walker HermitC g) => TransformH g a                   -> HPMInst a

newtype HPM a = HPM { unHPM :: ProgramT HPMInst PluginM a }
    deriving (Functor, Applicative, Monad, MonadIO)

runHPM :: PassInfo -> HPM () -> ModGuts -> CoreM ModGuts
runHPM passInfo hpass = scopedKernel $ \ kernel initSAST -> do
    ps <- defPS initSAST kernel passInfo
    (r,st) <- hpmToIO ps hpass
    let cleanup sast = do
            if sast /= initSAST -- only do this if we actually changed the AST
            then applyS kernel occurAnalyseAndDezombifyR (mkKernelEnv st) sast >>= resumeS kernel
            else resumeS kernel sast
    either (\case PAbort       -> abortS kernel
                  PResume sast -> cleanup sast
                  PError  err  -> putStrLn err >> abortS kernel)
           (\ _ -> cleanup $ ps_cursor st) r

hpmToIO :: PluginState -> HPM a -> IO (Either PException a, PluginState)
hpmToIO initState = runPluginT initState . eval . unHPM

eval :: ProgramT HPMInst PluginM a -> PluginM a
eval comp = do
    (kernel, env) <- gets $ ps_kernel &&& mkKernelEnv
    v <- viewT comp
    case v of
        Return x            -> return x
        RR rr       :>>= k  -> runS (applyS kernel rr env) >>= eval . k
        Query tr    :>>= k  -> runK (queryS kernel tr env) >>= eval . k
        Shell es os :>>= k -> do
            -- We want to discard the current focus, open the shell at
            -- the top level, then restore the current focus.
            paths <- resetScoping env
            clm (commandLine interpShellCommand os es)
            _ <- resetScoping env
            restoreScoping env paths
            eval $ k ()
        Guard p (HPM m)  :>>= k  -> gets (p . ps_pass) >>= \ b -> when b (eval m) >>= eval . k
        Focus tp (HPM m) :>>= k  -> do
            p <- runK (queryS kernel tp env)  -- run the pathfinding translation
            runS $ beginScopeS kernel         -- remember the current path
            runS $ modPathS kernel (<> p) env -- modify the current path
            r <- eval m             	      -- run the focused computation
            runS $ endScopeS kernel           -- endscope on it, so we go back to where we started
            eval $ k r

------------------------- Shell-related helpers --------------------------------------

resetScoping :: KernelEnv -> PluginM [PathH]
resetScoping env = do
    kernel <- gets ps_kernel
    paths <- runK $ pathS kernel
    replicateM_ (length paths - 1) $ runS $ endScopeS kernel
    -- modPathS commonly fails here because the path is unchanged, so throw away failures
    catchM (runS $ modPathS kernel (const mempty) env) (const (return ()))
    return paths

restoreScoping :: KernelEnv -> [PathH] -> PluginM ()
restoreScoping _   []    = return ()
restoreScoping env (h:t) = do
    kernel <- gets ps_kernel

    let go p []      = restore p
        go p (p':ps) = restore p >> runS (beginScopeS kernel) >> go p' ps

        -- modPathS commonly fails here because the path is unchanged, so throw away failures
        restore p = catchM (runS $ modPathS kernel (<> pathToSnocPath p) env)
                           (const (return ()))

    go h t

-- | Run a kernel function on the current SAST
runK :: (SAST -> PluginM a) -> PluginM a
runK f = gets ps_cursor >>= f

-- | Run a kernel function on the current SAST and update ps_cursor
runS :: (SAST -> PluginM SAST) -> PluginM ()
runS f = do
    sast <- runK f
    modify $ \st -> st { ps_cursor = sast }

interactive :: [External] -> [CommandLineOption] -> HPM ()
interactive es os = HPM . singleton $ Shell (externals ++ es) os

run :: (Injection GHC.ModGuts g, Walker HermitC g) => RewriteH g -> HPM ()
run = HPM . singleton . RR

query :: (Injection GHC.ModGuts g, Walker HermitC g) => TransformH g a -> HPM a
query = HPM . singleton . Query

----------------------------- guards ------------------------------

guard :: (PassInfo -> Bool) -> HPM () -> HPM ()
guard p = HPM . singleton . Guard p

at :: TransformH CoreTC LocalPathH -> HPM a -> HPM a
at tp = HPM . singleton . Focus tp

pass :: Int -> HPM () -> HPM ()
pass n = guard ((n ==) . passNum)

after :: CorePass -> HPM () -> HPM ()
after cp = guard (\passInfo -> case passesDone passInfo of
                            [] -> False
                            xs -> last xs == cp)

before :: CorePass -> HPM () -> HPM ()
before cp = guard (\passInfo -> case passesLeft passInfo of
                            (x:_) | cp == x -> True
                            _               -> False)

until :: CorePass -> HPM () -> HPM ()
until cp = guard ((cp `elem`) . passesLeft)

allPasses :: HPM () -> HPM ()
allPasses = guard (const True)

firstPass :: HPM () -> HPM ()
firstPass = guard (null . passesDone)

lastPass :: HPM () -> HPM ()
lastPass = guard (null . passesLeft)

----------------------------- other ------------------------------

getPassInfo :: HPM PassInfo
getPassInfo = HPM $ lift $ gets ps_pass

display :: HPM ()
display = HPM $ lift $ Display.display Nothing

modifyCLS :: (PluginState -> PluginState) -> HPM ()
modifyCLS = HPM . modify

setPretty :: PrettyPrinter -> HPM ()
setPretty pp = modifyCLS $ \s -> s { ps_pretty = pp }

setPrettyOptions :: PrettyOptions -> HPM ()
setPrettyOptions po = modifyCLS $ \s -> s { ps_pretty = (ps_pretty s) { pOptions = po } }
