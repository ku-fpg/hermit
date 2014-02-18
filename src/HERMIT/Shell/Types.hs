{-# LANGUAGE KindSignatures, GADTs, FlexibleContexts, TypeFamilies,
             DeriveDataTypeable, GeneralizedNewtypeDeriving, LambdaCase,
             ScopedTypeVariables #-}

module HERMIT.Shell.Types where

import Control.Applicative
import Control.Concurrent.STM
import Control.Monad.State
import Control.Monad.Error

import Data.Dynamic
import qualified Data.Map as M
import Data.Maybe (fromMaybe)
import Data.Monoid (mempty)

import HERMIT.Context
import HERMIT.Kure
import HERMIT.External
import qualified HERMIT.GHC as GHC
import HERMIT.Kernel.Scoped
import HERMIT.Monad
import HERMIT.Parser
import HERMIT.PrettyPrinter.Common

import HERMIT.Plugin.Display
import HERMIT.Plugin.Types

import HERMIT.Dictionary.Reasoning (CoreExprEquality)

import System.IO (Handle)
import System.Console.Terminfo (setupTermFromEnv, getCapability, termColumns, termLines)

----------------------------------------------------------------------------------

-- GADTs can't have docs on constructors. See Haddock ticket #43.
-- | KernelEffects are things that affect the state of the Kernel
--   - Apply a rewrite (giving a whole new lower-level AST).
--   - Change the current location using a computed path.
--   - Change the currect location using directions.
--   - Begin or end a scope.
--   - Delete an AST
--   - Run a precondition or other predicate that must not fail.
data KernelEffect :: * where
   Apply      :: (Injection GHC.ModGuts g, Walker HermitC g) => RewriteH g              -> KernelEffect
   Pathfinder :: (Injection GHC.ModGuts g, Walker HermitC g) => TranslateH g LocalPathH -> KernelEffect
   Direction  ::                                                Direction               -> KernelEffect
   BeginScope ::                                                                           KernelEffect
   EndScope   ::                                                                           KernelEffect
   Delete     ::                                                SAST                    -> KernelEffect
   CorrectnessCritera :: (Injection GHC.ModGuts g, Walker HermitC g) => TranslateH g () -> KernelEffect
   deriving Typeable

instance Extern KernelEffect where
   type Box KernelEffect = KernelEffect
   box i = i
   unbox i = i

----------------------------------------------------------------------------------

data QueryFun :: * where
   QueryString   :: (Injection GHC.ModGuts g, Walker HermitC g)
                 => TranslateH g String                                   -> QueryFun
   QueryDocH     :: (PrettyC -> PrettyH CoreTC -> TranslateH CoreTC DocH) -> QueryFun
   Diff          :: SAST -> SAST                                          -> QueryFun
   Display       ::                                                          QueryFun
   Inquiry       :: (CommandLineState -> IO String)                       -> QueryFun
   deriving Typeable

message :: String -> QueryFun
message str = Inquiry (const $ return str)

instance Extern QueryFun where
   type Box QueryFun = QueryFun
   box i = i
   unbox i = i

----------------------------------------------------------------------------------

type RewriteName = String

data ShellEffect
    = Abort -- ^ Abort GHC
    | CLSModify (CommandLineState -> IO CommandLineState) -- ^ Modify shell state
    | PluginComp (PluginM ())
    | Continue -- ^ exit the shell, but don't abort/resume
    | DefineScript ScriptName String
    | Dump String String Int
    | LoadFile ScriptName FilePath  -- load a file on top of the current node
    | RunScript ScriptName
    | SaveFile FilePath
    | SaveScript FilePath ScriptName
    | ScriptToRewrite RewriteName ScriptName
    | SeqMeta [ShellEffect]
    | Resume
    deriving Typeable

-- | A composite meta-command for running a loaded script immediately.
--   The script is given the same name as the filepath.
loadAndRun :: FilePath -> ShellEffect
loadAndRun fp = SeqMeta [LoadFile fp fp, RunScript fp]

instance Extern ShellEffect where
    type Box ShellEffect = ShellEffect
    box i = i
    unbox i = i

----------------------------------------------------------------------------------

data VersionCmd = Back                  -- back (up) the derivation tree
                | Step                  -- down one step; assumes only one choice
                | Goto Int              -- goto a specific node, if possible
                | GotoTag String        -- goto a specific named tag
                | AddTag String         -- add a tag
        deriving Show

----------------------------------------------------------------------------------

data CLException = CLAbort
                 | CLResume SAST
                 | CLContinue CommandLineState -- TODO: needed?
                 | CLError String

instance Error CLException where strMsg = CLError

abort :: Monad m => CLT m ()
abort = throwError CLAbort

resume :: Monad m => SAST -> CLT m ()
resume = throwError . CLResume

continue :: Monad m => CommandLineState -> CLT m ()
continue = throwError . CLContinue

rethrowCLE :: CLException -> PluginM a
rethrowCLE CLAbort         = throwError PAbort
rethrowCLE (CLResume sast) = throwError (PResume sast)
rethrowCLE (CLContinue s)  = put (cl_pstate s) >> return (error "CLContinue cannot return a value")
rethrowCLE (CLError msg)   = throwError (PError msg)

rethrowPE :: Monad m => PException -> CLT m a
rethrowPE PAbort         = throwError CLAbort
rethrowPE (PResume sast) = throwError (CLResume sast)
rethrowPE (PError msg)   = throwError (CLError msg)

----------------------------------------------------------------------------------

-- | This type is similiar to PluginM, except that its exception and state types are
-- supersets of those for PluginM, and it is a transformer. There are two functions: 
-- `clm` and `pluginM` for converting between the two. The reason we do this is to obtain 
-- a clean separation of plugin state from commandline state without nesting state 
-- transformers. Nesting StateT leads to a lot of awkward lifting and manual state 
-- management in the command line code.
--
-- NB: an alternative to monad transformers, like Oleg's Extensible Effects, might be useful here.
newtype CLT m a = CLT { unCLT :: ErrorT CLException (StateT CommandLineState m) a }
    deriving (Functor, Applicative, MonadIO, MonadError CLException, MonadState CommandLineState)

instance MonadTrans CLT where
    -- lift :: Monad m => m a -> CLT m a
    lift = CLT . lift . lift

-- TODO: type CLM = CLT IO

-- | Our own custom instance of Monad for CLT so we don't have to depend on
-- newtype deriving to do the right thing for fail.
instance Monad m => Monad (CLT m) where
    return = CLT . return
    (CLT m) >>= k = CLT (m >>= unCLT . k)
    fail = CLT . throwError . CLError

-- | Run a CLT computation.
runCLT :: CommandLineState -> CLT m a -> m (Either CLException a, CommandLineState)
runCLT s = flip runStateT s . runErrorT . unCLT

-- | Lift a CLM computation into the PluginM monad.
clm :: CLT IO a -> PluginM a
clm m = do
    s <- mkCLS
    (r,s') <- liftIO $ runCLT s m
    case r of
        Left err -> rethrowCLE err
        Right r' -> put (cl_pstate s') >> return r'

-- | Lift a PluginM computation into the CLM monad.
pluginM :: MonadIO m => PluginM a -> CLT m a
pluginM m = do
    s <- get
    (r,ps) <- liftIO $ runPluginT (cl_pstate s) m
    case r of
        Left err -> rethrowPE err
        Right r' -> put (s { cl_pstate = ps }) >> return r'

instance Monad m => MonadCatch (CLT m) where
    -- law: fail msg `catchM` f == f msg
    -- catchM :: m a -> (String -> m a) -> m a
    catchM m f = do
        st <- get
        (r,st') <- lift $ runCLT st m
        case r of
            Left err -> case err of
                            CLError msg -> f msg
                            other -> throwError other -- rethrow abort/resume/continue
            Right v  -> put st' >> return v

----------------------------------------------------------------------------------

data VersionStore = VersionStore
    { vs_graph       :: [(SAST,ExprH,SAST)]
    , vs_tags        :: [(String,SAST)]
    }

newSAST :: ExprH -> SAST -> CommandLineState -> CommandLineState
newSAST expr sast st = st { cl_pstate  = pstate  { ps_cursor = sast }
                          , cl_version = version { vs_graph = (ps_cursor pstate, expr, sast) : vs_graph version }
                          }
    where pstate  = cl_pstate st
          version = cl_version st

----------------------------------------------------------------------------------

-- Session-local issues; things that are never saved (except the PluginState).
data CommandLineState = CommandLineState
    { cl_pstate         :: PluginState           -- ^ Access to the enclosing plugin state. This is propagated back
                                                 --   to the plugin after the CLT computation ends. We do it this way
                                                 --   because nested StateT is a pain.
    , cl_height         :: Int                   -- ^ console height, in lines
    , cl_scripts        :: [(ScriptName,Script)]
    , cl_lemmas         :: [Lemma]               -- ^ list of lemmas, with flag indicating whether proven
    , cl_nav            :: Bool                  -- ^ keyboard input the nav panel
    , cl_version        :: VersionStore
    , cl_window         :: PathH                 -- ^ path to beginning of window, always a prefix of focus path in kernel
    , cl_dict           :: Dictionary
    -- this should be in a reader
    , cl_initSAST       :: SAST
    } deriving (Typeable)

-- To ease the pain of nested records, define some boilerplate here.
cl_corelint :: CommandLineState -> Bool
cl_corelint = ps_corelint . cl_pstate

setCoreLint :: CommandLineState -> Bool -> CommandLineState
setCoreLint st b = st { cl_pstate = (cl_pstate st) { ps_corelint = b } }

cl_cursor :: CommandLineState -> SAST
cl_cursor = ps_cursor . cl_pstate

setCursor :: CommandLineState -> SAST -> CommandLineState
setCursor st sast = st { cl_pstate = (cl_pstate st) { ps_cursor = sast } }

cl_diffonly :: CommandLineState -> Bool
cl_diffonly = ps_diffonly . cl_pstate

setDiffOnly :: CommandLineState -> Bool -> CommandLineState
setDiffOnly st b = st { cl_pstate = (cl_pstate st) { ps_diffonly = b } }

cl_failhard :: CommandLineState -> Bool
cl_failhard = ps_failhard . cl_pstate

setFailHard :: CommandLineState -> Bool -> CommandLineState
setFailHard st b = st { cl_pstate = (cl_pstate st) { ps_failhard = b } }

cl_kernel :: CommandLineState -> ScopedKernel
cl_kernel = ps_kernel . cl_pstate

cl_kernel_env :: CommandLineState -> HermitMEnv
cl_kernel_env = mkKernelEnv . cl_pstate

cl_pretty :: CommandLineState -> PrettyH CoreTC
cl_pretty = ps_pretty . cl_pstate

setPretty :: CommandLineState -> PrettyH CoreTC -> CommandLineState
setPretty st pp = st { cl_pstate = (cl_pstate st) { ps_pretty = pp } }

cl_pretty_opts :: CommandLineState -> PrettyOptions
cl_pretty_opts = ps_pretty_opts . cl_pstate

setPrettyOpts :: CommandLineState -> PrettyOptions -> CommandLineState
setPrettyOpts st po = st { cl_pstate = (cl_pstate st) { ps_pretty_opts = po } }

cl_render :: CommandLineState -> (Handle -> PrettyOptions -> Either String DocH -> IO ())
cl_render = ps_render . cl_pstate

cl_running_script :: CommandLineState -> Bool
cl_running_script = ps_running_script . cl_pstate

-- | Create default CommandLineState from PluginState. 
-- Note: the dictionary (cl_dict) will be empty, and should be populated if needed.
mkCLS :: PluginM CommandLineState
mkCLS = do
    ps <- get
    (w,h) <- liftIO getTermDimensions    
    return $ CommandLineState { cl_pstate   = (ps { ps_pretty_opts = (ps_pretty_opts ps) { po_width = w } })
                              , cl_height   = h
                              , cl_scripts  = []
                              , cl_lemmas   = []
                              , cl_nav      = False
                              , cl_version  = VersionStore { vs_graph = [] , vs_tags = [] }
                              , cl_window   = mempty
                              , cl_dict     = M.empty -- Note, empty dictionary.
                              , cl_initSAST = ps_cursor ps
                              }

getTermDimensions :: IO (Int, Int)
getTermDimensions = do
    term <- setupTermFromEnv
    let w = fromMaybe 80 $ getCapability term termColumns
        h = fromMaybe 30 $ getCapability term termLines
    return (w,h)

newtype CLSBox = CLSBox CommandLineState deriving Typeable
instance Extern CommandLineState where
    type Box CommandLineState = CLSBox
    unbox (CLSBox st) = st
    box = CLSBox

type ScriptName = String
type LemmaName = String
type Lemma = (LemmaName,CoreExprEquality,Bool)

-- tick counter
tick :: TVar (M.Map String Int) -> String -> IO Int
tick var msg = atomically $ do
        m <- readTVar var
        let c = case M.lookup msg m of
                    Nothing -> 1
                    Just x  -> x + 1
        writeTVar var (M.insert msg c m)
        return c

cl_putStr :: MonadIO m => String -> CLT m ()
cl_putStr = pluginM . ps_putStr

cl_putStrLn :: MonadIO m => String -> CLT m ()
cl_putStrLn = pluginM . ps_putStrLn
