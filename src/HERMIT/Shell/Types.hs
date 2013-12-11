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

import HERMIT.Context
import HERMIT.Kure
import HERMIT.External
import qualified HERMIT.GHC as GHC
import HERMIT.Kernel.Scoped
import HERMIT.Monad
import HERMIT.Parser
import HERMIT.PrettyPrinter.Common

import HERMIT.Dictionary.Reasoning (CoreExprEquality)

import System.IO

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
                 | CLContinue CommandLineState
                 | CLError String

instance Error CLException where
    strMsg = CLError

newtype CLM m a = CLM { unCLM :: ErrorT CLException (StateT CommandLineState m) a }
    deriving (Functor, Applicative, MonadIO, MonadError CLException, MonadState CommandLineState)

-- | Our own custom instance of Monad for CLM m so we don't have to depend on
-- newtype deriving to do the right thing for fail.
instance Monad m => Monad (CLM m) where
    return = CLM . return
    (CLM m) >>= k = CLM (m >>= unCLM . k)
    fail = CLM . throwError . CLError

abort :: Monad m => CLM m ()
abort = throwError CLAbort

resume :: Monad m => SAST -> CLM m ()
resume = throwError . CLResume

continue :: Monad m => CommandLineState -> CLM m ()
continue = throwError . CLContinue

instance MonadTrans CLM where
    lift = CLM . lift . lift

instance Monad m => MonadCatch (CLM m) where
    -- law: fail msg `catchM` f == f msg
    -- catchM :: m a -> (String -> m a) -> m a
    catchM m f = do
        st <- get
        (r,st') <- lift $ runCLM st m
        case r of
            Left err -> case err of
                            CLError msg -> f msg
                            other -> throwError other -- rethrow abort/resume
            Right v  -> put st' >> return v

runCLM :: CommandLineState -> CLM m a -> m (Either CLException a, CommandLineState)
runCLM s = flip runStateT s . runErrorT . unCLM

-- TODO: Come up with names for these, and/or better characterise these abstractions.
iokm2clm' :: MonadIO m => String -> (a -> CLM m b) -> IO (KureM a) -> CLM m b
iokm2clm' msg ret m = liftIO m >>= runKureM ret (throwError . CLError . (msg ++))

iokm2clm :: MonadIO m => String -> IO (KureM a) -> CLM m a
iokm2clm msg = iokm2clm' msg return

iokm2clm'' :: MonadIO m => IO (KureM a) -> CLM m a
iokm2clm'' = iokm2clm ""

----------------------------------------------------------------------------------

data VersionStore = VersionStore
    { vs_graph       :: [(SAST,ExprH,SAST)]
    , vs_tags        :: [(String,SAST)]
    }

newSAST :: ExprH -> SAST -> CommandLineState -> CommandLineState
newSAST expr sast st = st { cl_cursor = sast
                          , cl_version = (cl_version st) { vs_graph = (cl_cursor st, expr, sast) : vs_graph (cl_version st) }
                          }

----------------------------------------------------------------------------------

-- Session-local issues; things that are never saved.
data CommandLineState = CommandLineState
    { cl_cursor         :: SAST                                     -- ^ the current AST
    , cl_pretty         :: PrettyH CoreTC                           -- ^ which pretty printer to use
    , cl_pretty_opts    :: PrettyOptions                            -- ^ the options for the pretty printer
    , cl_render         :: Handle -> PrettyOptions -> Either String DocH -> IO () -- ^ the way of outputing to the screen
    , cl_height         :: Int                                      -- ^ console height, in lines
    , cl_nav            :: Bool                                     -- ^ keyboard input the nav panel
    , cl_running_script :: Bool                                     -- ^ if running a script
    , cl_tick           :: TVar (M.Map String Int)                  -- ^ the list of ticked messages
    , cl_corelint       :: Bool                                     -- ^ if true, run Core Lint on module after each rewrite
    , cl_diffonly       :: Bool                                     -- ^ if true, show diffs rather than pp full code
    , cl_failhard       :: Bool                                     -- ^ if true, abort on *any* failure
    , cl_window         :: PathH                                    -- ^ path to beginning of window, always a prefix of focus path in kernel
    , cl_scripts        :: [(ScriptName,Script)]
    , cl_lemmas         :: [Lemma]                                  -- ^ list of lemmas, with flag indicating whether proven
    -- these three should be in a reader
    , cl_dict           :: Dictionary
    , cl_kernel         :: ScopedKernel
    , cl_initSAST       :: SAST
    -- and the version store
    , cl_version        :: VersionStore
    } deriving (Typeable)

newtype CLSBox = CLSBox CommandLineState deriving Typeable
instance Extern CommandLineState where
    type Box CommandLineState = CLSBox
    unbox (CLSBox st) = st
    box = CLSBox

type ScriptName = String
type LemmaName = String
type Lemma = (LemmaName,CoreExprEquality,Bool)

cl_kernel_env  :: CommandLineState -> HermitMEnv
cl_kernel_env st =
    let out str = do (r,_) <- liftIO $ runCLM st $ cl_putStrLn str
                     either (\case CLError msg -> fail msg
                                   _           -> fail "resume/abort/continue called from cl_putStrLn (impossible!)")
                            return r

    in  mkHermitMEnv $ \ msg -> case msg of
                DebugTick    msg'      -> do
                        c <- liftIO $ tick (cl_tick st) msg'
                        out $ "<" ++ show c ++ "> " ++ msg'
                DebugCore  msg' cxt core -> do
                        out $ "[" ++ msg' ++ "]"
                        doc :: DocH <- apply (cl_pretty st) (liftPrettyC (cl_pretty_opts st) cxt) (inject core)
                        liftIO $ cl_render st stdout (cl_pretty_opts st) (Right doc)

-- tick counter
tick :: TVar (M.Map String Int) -> String -> IO Int
tick var msg = atomically $ do
        m <- readTVar var
        let c = case M.lookup msg m of
                Nothing -> 1
                Just x  -> x + 1
        writeTVar var (M.insert msg c m)
        return c

cl_putStr :: MonadIO m => String -> CLM m ()
cl_putStr str = do
    st <- get
    liftIO $ cl_render st stdout (cl_pretty_opts st) (Left str)

cl_putStrLn :: MonadIO m => String -> CLM m ()
cl_putStrLn = cl_putStr . (++"\n")

