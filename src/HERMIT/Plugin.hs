{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

module HERMIT.Plugin
    ( -- * The HERMIT Plugin
      hermitPlugin
      -- ** Stateful reflection of Kernel API
    , abort
    , resume
    , query
    , apply
    , delete
    , list
    , tell
      -- ** Using the shell
    , interactive
    , display
    , setPretty
    , setPrettyOptions
      -- ** Active modifiers
    , pass
    , after
    , before
    , until
    , allPasses
    , firstPass
    , lastPass
      -- ** Knobs and Dials
    , getPassInfo
    , getKernel
    ) where

import Control.Concurrent.STM
import Control.Monad (when)
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Reader (asks)
import Control.Monad.State (gets, modify)
import Control.Monad.Error.Class

import qualified Data.Map as M

import HERMIT.Dictionary
import HERMIT.External
import HERMIT.Kernel
import HERMIT.Context
import HERMIT.Kure hiding (apply)
#if __GLASGOW_HASKELL__ < 710
import HERMIT.GHC hiding (singleton, liftIO, display)
#else
import HERMIT.GHC hiding (singleton, liftIO)
#endif
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

hermitPlugin :: ([CommandLineOption] -> PluginM ()) -> Plugin
hermitPlugin f = buildPlugin $ \ store passInfo opts -> do
    hermitKernel store (lpName passInfo) $ \ kernel initAST -> do
        ps <- defPS initAST
        (r,st) <- runPluginT (PluginReader kernel passInfo) ps $ f opts
        let cleanup ast = do
                if ast /= initAST -- only do this if we actually changed the AST
                then applyK kernel (extractR (occurAnalyseAndDezombifyR :: RewriteH Core)) Never (mkKernelEnv st) ast >>= resumeK kernel
                else resumeK kernel ast
        either (\case PAbort      -> abortK kernel
                      PResume ast -> cleanup ast
                      PError  err -> putStrLn err >> abortK kernel)
               (\ _ -> cleanup $ ps_cursor st) r

defPS :: AST -> IO PluginState
defPS initAST = do
    emptyTick <- liftIO $ atomically $ newTVar M.empty
    return $ PluginState
                { ps_cursor         = initAST
                , ps_pretty         = Clean.pretty
                , ps_render         = unicodeConsole
                , ps_tick           = emptyTick
                , ps_corelint       = False
                }

lpName :: PassInfo -> String
lpName pInfo = case passesDone pInfo of
                    [] -> "-- front end" -- comment format in case these appear in dumped script
                    ps -> "-- GHC - " ++ show (last ps)

------------------------- Shell-related helpers --------------------------------------

-- | Run a PluginM function on the current AST and update ps_cursor
runA :: (AST -> PluginM AST) -> PluginM ()
runA f = runQ (fmap (,()) . f)

-- | Run a PluginM function on the current AST, update ps_cursor, return result
runQ :: (AST -> PluginM (AST, a)) -> PluginM a
runQ f = do
    (sast, r) <- gets ps_cursor >>= f
    modify $ \st -> st { ps_cursor = sast }
    return r

interactive :: [External] -> [CommandLineOption] -> PluginM ()
interactive es os = clm $ commandLine os (externals ++ es)

abort :: PluginM a
abort = throwError PAbort

resume :: PluginM a
resume = gets ps_cursor >>= throwError . PResume

apply :: (Injection GHC.ModGuts g, Walker HermitC g) => CommitMsg -> RewriteH g -> PluginM ()
apply cm rr = do
    kernel <- asks pr_kernel
    env <- gets mkKernelEnv
    runA (applyK kernel (extractR rr) cm env)

query :: (Injection GHC.ModGuts g, Walker HermitC g) => CommitMsg -> TransformH g a -> PluginM a
query cm tr = do
    kernel <- asks pr_kernel
    env <- gets mkKernelEnv
    runQ (queryK kernel (extractT tr) cm env)

list :: PluginM [(AST,Maybe String, Maybe AST)]
list = asks pr_kernel >>= listK

delete :: AST -> PluginM ()
delete ast = do
    k <- asks pr_kernel
    cursor <- gets ps_cursor
    if ast == cursor
    then do
        l <- list
        case [ p | (ast',_,Just p) <- l, ast' == ast ] of
            [ast'] -> do modify $ \ st -> st { ps_cursor = ast' }
                         deleteK k ast
            _ -> fail "cannot delete current AST because it has no parent."
    else deleteK k ast

tell :: String -> PluginM ()
tell str = do
    k <- asks pr_kernel
    runA (tellK k str)

----------------------------- guards ------------------------------

guard :: (PassInfo -> Bool) -> PluginM () -> PluginM ()
guard p m = do
    b <- asks (p . pr_pass)
    when b m

pass :: Int -> PluginM () -> PluginM ()
pass n = guard ((n ==) . passNum)

after :: CorePass -> PluginM () -> PluginM ()
after cp = guard (\passInfo -> case passesDone passInfo of
                            [] -> False
                            xs -> last xs == cp)

before :: CorePass -> PluginM () -> PluginM ()
before cp = guard (\passInfo -> case passesLeft passInfo of
                            (x:_) | cp == x -> True
                            _               -> False)

until :: CorePass -> PluginM () -> PluginM ()
until cp = guard ((cp `elem`) . passesLeft)

allPasses :: PluginM () -> PluginM ()
allPasses = guard (const True)

firstPass :: PluginM () -> PluginM ()
firstPass = guard (null . passesDone)

lastPass :: PluginM () -> PluginM ()
lastPass = guard (null . passesLeft)

----------------------------- other ------------------------------

getKernel :: PluginM Kernel
getKernel = asks pr_kernel

getPassInfo :: PluginM PassInfo
getPassInfo = asks pr_pass

display :: PluginM ()
display = Display.display Nothing Nothing

setPretty :: PrettyPrinter -> PluginM ()
setPretty pp = modify $ \s -> s { ps_pretty = pp }

setPrettyOptions :: PrettyOptions -> PluginM ()
setPrettyOptions po = modify $ \s -> s { ps_pretty = (ps_pretty s) { pOptions = po } }
