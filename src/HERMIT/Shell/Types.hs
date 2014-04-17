{-# LANGUAGE CPP, KindSignatures, GADTs, FlexibleContexts, DeriveDataTypeable, 
             FunctionalDependencies, GeneralizedNewtypeDeriving, InstanceSigs,
             LambdaCase, RankNTypes, ScopedTypeVariables, TypeFamilies #-}

module HERMIT.Shell.Types where

import Control.Applicative
import Control.Arrow
import Control.Concurrent
import Control.Concurrent.STM
import Control.Monad.State
import Control.Monad.Error

import Data.Char (isSpace)
import Data.Dynamic
import Data.List (intercalate, isPrefixOf, nub)
import qualified Data.Map as M
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

import HERMIT.Dictionary.Inline
import HERMIT.Dictionary.Navigation
import HERMIT.Dictionary.Reasoning (CoreExprEquality)

import System.Console.Haskeline hiding (catch, display)
import System.IO (Handle)

#ifndef mingw32_HOST_OS
import Data.Maybe (fromMaybe)
import System.Console.Terminfo (setupTermFromEnv, getCapability, termColumns, termLines)
#endif

----------------------------------------------------------------------------------

{-
-- | How to perform a given set of commands.
--
-- Mnemonic:
-- c = command type
-- a = extra arguments type (use tuple for more than one)
-- r = result type
--
-- Often, a and r are (), but sometimes we need more clever things.
class ShellCommandSet c a r | c -> a r where
    performCommand :: (MonadCatch m, MonadError CLException m, MonadIO m, MonadState CommandLineState m) => c -> a -> m r
-}

----------------------------------------------------------------------------------

data QueryFun :: * where
   QueryString   :: (Injection GHC.ModGuts g, Walker HermitC g)
                 => TransformH g String                                   -> QueryFun
   QueryDocH     :: (PrettyC -> PrettyH CoreTC -> TransformH CoreTC DocH) -> QueryFun
   Diff          :: SAST -> SAST                                          -> QueryFun
   Display       ::                                                          QueryFun
   Inquiry       :: (CommandLineState -> IO String)                       -> QueryFun
   CorrectnessCritera :: (Injection GHC.ModGuts g, Walker HermitC g) => TransformH g () -> QueryFun
   deriving Typeable

message :: String -> QueryFun
message str = Inquiry (const $ return str)

instance Extern QueryFun where
   type Box QueryFun = QueryFun
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

abort :: MonadError CLException m => m ()
abort = throwError CLAbort

resume :: MonadError CLException m => SAST -> m ()
resume = throwError . CLResume

continue :: MonadError CLException m => CommandLineState -> m ()
continue = throwError . CLContinue

rethrowCLE :: CLException -> PluginM a
rethrowCLE CLAbort         = throwError PAbort
rethrowCLE (CLResume sast) = throwError (PResume sast)
rethrowCLE (CLContinue s)  = put (cl_pstate s) >> return (error "CLContinue cannot return a value")
rethrowCLE (CLError msg)   = throwError (PError msg)

rethrowPE :: MonadError CLException m => PException -> m a
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

-- | Lift a CLT IO computation into a CLT computation over an arbitrary MonadIO.
clm2clt :: MonadIO m => CLT IO a -> CLT m a
clm2clt m = do
    st <- get
    (ea, st') <- liftIO (runCLT st m)
    either throwError (\r -> put st' >> return r) ea

-- | Lift a CLM computation into the PluginM monad.
clm :: CLT IO a -> PluginM a
clm m = do
    s <- mkCLS
    (r,s') <- liftIO $ runCLT s m
    case r of
        Left err -> rethrowCLE err
        Right r' -> put (cl_pstate s') >> return r'

-- | Lift a PluginM computation into the CLM monad.
pluginM :: (MonadError CLException m, MonadIO m, MonadState CommandLineState m) => PluginM a -> m a
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
#ifdef mingw32_HOST_OS
    return (80,25) -- these are the standard windows CLI dimensions
#else
    term <- setupTermFromEnv
    let w = fromMaybe 80 $ getCapability term termColumns
        h = fromMaybe 25 $ getCapability term termLines
    return (w,h)
#endif

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

cl_putStr :: (MonadError CLException m, MonadIO m, MonadState CommandLineState m) => String -> m ()
cl_putStr = pluginM . ps_putStr

cl_putStrLn :: (MonadError CLException m, MonadIO m, MonadState CommandLineState m) => String -> m ()
cl_putStrLn = pluginM . ps_putStrLn

-- TODO: rename?
putStrToConsole :: (MonadError CLException m, MonadIO m, MonadState CommandLineState m) => String -> m ()
putStrToConsole str = ifM (gets cl_running_script)
                          (return ())
                          (cl_putStrLn str)

------------------------------------------------------------------------------

shellComplete :: MVar CommandLineState -> String -> String -> IO [Completion]
shellComplete mvar rPrev so_far = do
    st <- readMVar mvar
    targetQuery <- completionQuery st (completionType rPrev)
    -- (liftM.liftM) (map simpleCompletion . nub . filter (so_far `isPrefixOf`))
    --     $ queryS (cl_kernel st) (cl_cursor (cl_session st)) targetQuery
    -- TODO: I expect you want to build a silent version of the kernal_env for this query
    cl <- catchM (queryS (cl_kernel st) targetQuery (cl_kernel_env st) (cl_cursor st)) (\_ -> return [])
    return $ (map simpleCompletion . nub . filter (so_far `isPrefixOf`)) cl

data CompletionType = ConsiderC       -- considerable constructs and (deprecated) bindingOfT
                    | BindingOfC      -- bindingOfT
                    | BindingGroupOfC -- bindingGroupOfT
                    | RhsOfC          -- rhsOfT
                    | OccurrenceOfC   -- occurrenceOfT
                    | InlineC         -- complete with names that can be inlined
                    | CommandC        -- complete using dictionary commands (default)
                    | AmbiguousC [CompletionType]  -- completionType function needs to be more specific
    deriving (Show)

-- TODO: reverse rPrev and parse it, to better figure out what possiblities are in context?
--       for instance, completing "any-bu (inline " should be different than completing just "inline "
--       this would also allow typed completion?
completionType :: String -> CompletionType
completionType = go . dropWhile isSpace
    where go rPrev = case [ ty | (nm, ty) <- opts, reverse nm `isPrefixOf` rPrev ] of
                        []  -> CommandC
                        [t] -> t
                        ts  -> AmbiguousC ts
          opts = [ ("inline"          , InlineC  )
                 , ("consider"        , ConsiderC)
                 , ("binding-of"      , BindingOfC)
                 , ("binding-group-of", BindingGroupOfC)
                 , ("rhs-of"          , RhsOfC)
                 , ("occurrence-of"   , OccurrenceOfC)
                 ]

completionQuery :: CommandLineState -> CompletionType -> IO (TransformH CoreTC [String])
completionQuery _ ConsiderC       = return $ bindingOfTargetsT       >>^ GHC.varSetToStrings >>^ map ('\'':) >>^ (++ map fst considerables) -- the use of bindingOfTargetsT here is deprecated
completionQuery _ OccurrenceOfC   = return $ occurrenceOfTargetsT    >>^ GHC.varSetToStrings >>^ map ('\'':)
completionQuery _ BindingOfC      = return $ bindingOfTargetsT       >>^ GHC.varSetToStrings >>^ map ('\'':)
completionQuery _ BindingGroupOfC = return $ bindingGroupOfTargetsT  >>^ GHC.varSetToStrings >>^ map ('\'':)
completionQuery _ RhsOfC          = return $ rhsOfTargetsT           >>^ GHC.varSetToStrings >>^ map ('\'':)
completionQuery _ InlineC         = return $ promoteT inlineTargetsT >>^                         map ('\'':)
completionQuery s CommandC        = return $ pure (M.keys (cl_dict s))
-- Need to modify opts in completionType function. No key can be a suffix of another key.
completionQuery _ (AmbiguousC ts) = do
    putStrLn "\nCannot tab complete: ambiguous completion type."
    putStrLn $ "Possibilities: " ++ intercalate ", " (map show ts)
    return (pure [])

------------------------------------------------------------------------------

fixWindow :: (MonadError CLException m, MonadIO m, MonadState CommandLineState m) => m ()
fixWindow = do
    st <- get
    -- check to make sure new path is still inside window
    focusPath <- pluginM getFocusPath
    -- move the window in two cases:
    --  1. window path is not prefix of focus path
    --  2. window path is empty (since at the top level we only show type sigs)
    {- when (not (isPrefixOf (cl_window st) focusPath) || null (cl_window st))
       $ put $ st { cl_window = focusPath } -}
    put $ st { cl_window = focusPath } -- TODO: temporary until we figure out a better highlight interface

showWindow :: (MonadError CLException m, MonadIO m, MonadState CommandLineState m) => m ()
showWindow = fixWindow >> gets cl_window >>= pluginM . display . Just

------------------------------------------------------------------------------

showGraph :: [(SAST,ExprH,SAST)] -> [(String,SAST)] -> SAST -> String
showGraph graph tags this@(SAST n) =
        (if length paths > 1 then "tag " ++ show n ++ "\n" else "") ++
        concat (intercalate
                ["goto " ++ show n ++ "\n"]
                [ [ unparseExprH b ++ "\n" ++ showGraph graph tags c ]
                | (b,c) <- paths
                ])
  where  
          paths = [ (b,c) | (a,b,c) <- graph, a == this ]

------------------------------------------------------------------------------

{-
data CmdInterps :: * where
    CmdInterps :: forall c a r. ShellCommandSet c a r => [Interp c] -> CmdInterps

instance ShellCommandSet () () () where
    performCommand = const return
-}
