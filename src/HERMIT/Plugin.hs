{-# LANGUAGE KindSignatures, GADTs, FlexibleContexts, GeneralizedNewtypeDeriving, LambdaCase #-}
{-# LANGUAGE TupleSections #-}
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
import Control.Monad (when)
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Operational
import Control.Monad.State (gets, modify)
import Control.Monad.Trans.Class (MonadTrans(..))

import Data.IORef
import qualified Data.Map as M
import Data.Monoid

import HERMIT.Dictionary
import HERMIT.External hiding (Query, Shell)
import HERMIT.Kernel
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
hermitPlugin f = buildPlugin $ \ store passInfo -> runHPM store passInfo . f

defPS :: AST -> Kernel -> PassInfo -> IO PluginState
defPS initAST kernel passInfo = do
    emptyTick <- liftIO $ atomically $ newTVar M.empty
    return $ PluginState
                { ps_cursor         = initAST
                , ps_focus          = mempty
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

lpName :: PassInfo -> String
lpName pInfo = case passesDone pInfo of
                    [] -> "-- front end" -- comment format in case these appear in dumped script
                    ps -> "-- GHC - " ++ show (last ps)

runHPM :: IORef (Maybe (AST, ASTMap)) -> PassInfo -> HPM () -> ModGuts -> CoreM ModGuts
runHPM store passInfo hpass = hermitKernel store (lpName passInfo) $ \ kernel initAST -> do
    ps <- defPS initAST kernel passInfo
    (r,st) <- hpmToIO ps hpass
    let cleanup ast = do
            if ast /= initAST -- only do this if we actually changed the AST
            then applyK kernel (extractR occurAnalyseAndDezombifyR) Never (mkKernelEnv st) ast >>= resumeK kernel
            else resumeK kernel ast
    either (\case PAbort      -> abortK kernel
                  PResume ast -> cleanup ast
                  PError  err -> putStrLn err >> abortK kernel)
           (\ _ -> cleanup $ ps_cursor st) r

hpmToIO :: PluginState -> HPM a -> IO (Either PException a, PluginState)
hpmToIO initState = runPluginT initState . eval . unHPM

eval :: ProgramT HPMInst PluginM a -> PluginM a
eval comp = do
    (kernel, (env, path)) <- gets $ ps_kernel &&& mkKernelEnv &&& ps_focus
    v <- viewT comp
    case v of
        Return x           -> return x
        RR rr       :>>= k -> runS (applyK kernel (extractR $ localPathR path rr) Never env) >>= eval . k
        Query tr    :>>= k -> runQ (queryK kernel (extractT $ localPathT path tr) Never env) >>= eval . k
        Shell es os :>>= k -> clm (commandLine os es) >>= eval . k
        Guard p (HPM m)  :>>= k  -> gets (p . ps_pass) >>= \ b -> when b (eval m) >>= eval . k
        Focus tp (HPM m) :>>= k  -> do
            p <- runQ (queryK kernel (extractT tp) Never env)  -- run the pathfinding translation
            old_p <- gets ps_focus
            modify $ \st -> st { ps_focus = old_p <> p }
            r <- eval m             	      -- run the focused computation
            modify $ \st -> st { ps_focus = old_p }
            eval $ k r

------------------------- Shell-related helpers --------------------------------------

-- | Run a kernel function on the current AST
runK :: (AST -> PluginM a) -> PluginM a
runK f = gets ps_cursor >>= f

-- | Run a kernel function on the current AST and update ps_cursor
runS :: (AST -> PluginM AST) -> PluginM ()
runS f = runQ (fmap (,()) . f)

runQ :: (AST -> PluginM (AST, a)) -> PluginM a
runQ f = do
    (sast, r) <- runK f
    modify $ \st -> st { ps_cursor = sast }
    return r

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
display = HPM $ lift $ Display.display Nothing Nothing

modifyCLS :: (PluginState -> PluginState) -> HPM ()
modifyCLS = HPM . modify

setPretty :: PrettyPrinter -> HPM ()
setPretty pp = modifyCLS $ \s -> s { ps_pretty = pp }

setPrettyOptions :: PrettyOptions -> HPM ()
setPrettyOptions po = modifyCLS $ \s -> s { ps_pretty = (ps_pretty s) { pOptions = po } }
