{-# LANGUAGE ConstraintKinds, CPP, KindSignatures, GADTs, FlexibleContexts, DeriveDataTypeable,
             FunctionalDependencies, GeneralizedNewtypeDeriving, InstanceSigs,
             LambdaCase, RankNTypes, ScopedTypeVariables, TypeFamilies #-}

module HERMIT.Shell.Types where

import Control.Applicative
import Control.Arrow
import Control.Concurrent.STM
import Control.Monad.State
#if MIN_VERSION_mtl(2,2,1)
import Control.Monad.Except
#else
import Control.Monad.Error
#endif

import Data.Char (isSpace)
import Data.Dynamic
import Data.List (intercalate, isPrefixOf, nub)
import qualified Data.Map as M
import Data.Maybe (fromMaybe, isJust)
import Data.Monoid (mempty)

import HERMIT.Context
import HERMIT.Core
import HERMIT.Kure
import HERMIT.External
import qualified HERMIT.GHC as GHC
import HERMIT.Kernel (AST, queryK)
import HERMIT.Kernel.Scoped
import HERMIT.Monad
import HERMIT.Parser
import HERMIT.PrettyPrinter.Common

import HERMIT.Plugin.Display
import HERMIT.Plugin.Renderer
import HERMIT.Plugin.Types

import HERMIT.Dictionary.Inline
import HERMIT.Dictionary.Navigation

import System.Console.Haskeline hiding (catch, display)
import System.IO (Handle, stdout)

#ifdef mingw32_HOST_OS
import HERMIT.Win32.Console
#else
import System.Console.Terminfo (setupTermFromEnv, getCapability, termColumns, termLines)
#endif

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

performQuery :: (MonadCatch m, CLMonad m) => QueryFun -> ExprH -> m ()

performQuery (QueryString q) _ = do
    st <- get
    str <- prefixFailMsg "Query failed: " $ queryS (cl_kernel st) q (cl_kernel_env st) (cl_cursor st)
    putStrToConsole str

performQuery (QueryDocH q) _ = do
    st <- get
    doc <- prefixFailMsg "Query failed: " $ queryS (cl_kernel st) (q (initPrettyC $ cl_pretty_opts st) $ pCoreTC $ cl_pretty st) (cl_kernel_env st) (cl_cursor st)
    liftIO $ cl_render st stdout (cl_pretty_opts st) (Right doc)

performQuery (Inquiry f) _ = get >>= liftIO . f >>= putStrToConsole

performQuery (Diff s1 s2) _ = do
    st <- get

    ast1 <- toASTS (cl_kernel st) s1
    ast2 <- toASTS (cl_kernel st) s2
    let getCmds sast | sast == s1 = []
                     | otherwise = case [ (f,c) | (f,c,to) <- vs_graph (cl_version st), to == sast ] of
                                    [(sast',cmd)] -> unparseExprH cmd : getCmds sast'
                                    _ -> ["error: history broken!"] -- should be impossible

    cl_putStrLn "Commands:"
    cl_putStrLn "========="
    cl_putStrLn $ unlines $ reverse $ getCmds s2

    doc1 <- ppWholeProgram ast1
    doc2 <- ppWholeProgram ast2

    r <- diffDocH (cl_pretty st) doc1 doc2

    cl_putStrLn "Diff:"
    cl_putStrLn "====="
    cl_putStr r

-- Explicit calls to display should work no matter what the loading state is.
performQuery Display _ = do
    running_script_st <- gets cl_running_script
    setRunningScript Nothing
    showWindow
    setRunningScript running_script_st

performQuery (CorrectnessCritera q) expr = do
    st <- get
    -- TODO: Again, we may want a quiet version of the kernel_env
    modFailMsg (\ err -> unparseExprH expr ++ " [exception: " ++ err ++ "]")
        $ queryS (cl_kernel st) q (cl_kernel_env st) (cl_cursor st)
    putStrToConsole $ unparseExprH expr ++ " [correct]"

ppWholeProgram :: (MonadIO m, MonadState CommandLineState m) => AST -> m DocH
ppWholeProgram ast = do
    st <- get
    liftIO (queryK (kernelS $ cl_kernel st)
            ast
            (extractT $ pathT [ModGuts_Prog] $ liftPrettyH (cl_pretty_opts st) $ pCoreTC $ cl_pretty st)
            (cl_kernel_env st)) >>= runKureM return fail

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

#if !(MIN_VERSION_mtl(2,2,1))
instance Error CLException where strMsg = CLError
#endif

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
#if MIN_VERSION_mtl(2,2,1)
newtype CLT m a = CLT { unCLT :: ExceptT CLException (StateT CommandLineState m) a }
#else
newtype CLT m a = CLT { unCLT :: ErrorT CLException (StateT CommandLineState m) a }
#endif
    deriving (Functor, Applicative, MonadIO, MonadError CLException, MonadState CommandLineState)

-- Adapted from System.Console.Haskeline.MonadException, which hasn't provided an instance for ExceptT yet
#if MIN_VERSION_mtl(2,2,1)
instance MonadException m => MonadException (ExceptT e m) where
    controlIO f = ExceptT $ controlIO $ \(RunIO run) -> let
                    run' = RunIO (fmap ExceptT . run . runExceptT)
                    in fmap runExceptT $ f run'
#endif

instance MonadException m => MonadException (CLT m) where
    controlIO f = CLT $ controlIO $ \(RunIO run) -> let run' = RunIO (fmap CLT . run . unCLT)
                                                    in fmap unCLT $ f run'

-- This is copied verbatim from Haskeline, which provides an instance for strict State only.
-- This allows lazy State to enjoy the same benefits.
instance MonadException m => MonadException (StateT s m) where
    controlIO f = StateT $ \s -> controlIO $ \(RunIO run) -> let
                    run' = RunIO (fmap (StateT . const) . run . flip runStateT s)
                    in fmap (flip runStateT s) $ f run'

type CLMonad m = (MonadIO m, MonadState CommandLineState m, MonadError CLException m)

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
#if MIN_VERSION_mtl(2,2,1)
runCLT s = flip runStateT s . runExceptT . unCLT
#else
runCLT s = flip runStateT s . runErrorT . unCLT
#endif

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
pluginM :: CLMonad m => PluginM a -> m a
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

newSAST :: ExprH -> SAST -> [Lemma] -> CommandLineState -> CommandLineState
newSAST expr sast ls st = st { cl_pstate  = pstate  { ps_cursor = sast }
                             , cl_version = version { vs_graph = (ps_cursor pstate, expr, sast) : vs_graph version }
                             , cl_lemmas  = ls ++ cl_lemmas st
                             }
    where pstate  = cl_pstate st
          version = cl_version st

----------------------------------------------------------------------------------

-- Session-local issues; things that are never saved (except the PluginState).
data CommandLineState = CommandLineState
    { cl_pstate         :: PluginState            -- ^ Access to the enclosing plugin state. This is propagated back
                                                  --   to the plugin after the CLT computation ends. We do it this way
                                                  --   because nested StateT is a pain.
    , cl_height         :: Int                    -- ^ console height, in lines
    , cl_scripts        :: [(ScriptName,Script)]
    , cl_lemmas         :: [Lemma]                -- ^ list of lemmas, with flag indicating whether proven
    , cl_nav            :: Bool                   -- ^ keyboard input the nav panel
    , cl_version        :: VersionStore
    , cl_window         :: PathH                  -- ^ path to beginning of window, always a prefix of focus path in kernel
    , cl_externals      :: [External]             -- ^ Currently visible externals
    , cl_running_script :: Maybe Script           -- ^ Nothing = no script running, otherwise the remaining script commands
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

cl_pretty :: CommandLineState -> PrettyPrinter
cl_pretty = ps_pretty . cl_pstate

setPretty :: CommandLineState -> PrettyPrinter -> CommandLineState
setPretty st pp = st { cl_pstate = (cl_pstate st) { ps_pretty = pp } }

cl_pretty_opts :: CommandLineState -> PrettyOptions
cl_pretty_opts = pOptions . cl_pretty

setPrettyOpts :: CommandLineState -> PrettyOptions -> CommandLineState
setPrettyOpts st po = setPretty st $ (cl_pretty st) { pOptions = po }

cl_render :: CommandLineState -> (Handle -> PrettyOptions -> Either String DocH -> IO ())
cl_render = ps_render . cl_pstate

-- | Create default CommandLineState from PluginState.
-- Note: the dictionary (cl_dict) will be empty, and should be populated if needed.
mkCLS :: PluginM CommandLineState
mkCLS = do
    ps <- get
    (w,h) <- liftIO getTermDimensions
    let st = CommandLineState { cl_pstate         = ps
                              , cl_height         = h
                              , cl_scripts        = []
                              , cl_lemmas         = []
                              , cl_nav            = False
                              , cl_version        = VersionStore { vs_graph = [] , vs_tags = [] }
                              , cl_window         = mempty
                              , cl_externals      = [] -- Note, empty dictionary.
                              , cl_running_script = Nothing
                              , cl_initSAST       = ps_cursor ps
                              }
    return $ setPrettyOpts st $ (cl_pretty_opts st) { po_width = w }

getTermDimensions :: IO (Int, Int)
getTermDimensions = do
#ifdef mingw32_HOST_OS
    consoleSz <- getConsoleWindowSize
    return $ fromMaybe (80,25) consoleSz
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

-- tick counter
tick :: TVar (M.Map String Int) -> String -> IO Int
tick var msg = atomically $ do
        m <- readTVar var
        let c = case M.lookup msg m of
                    Nothing -> 1
                    Just x  -> x + 1
        writeTVar var (M.insert msg c m)
        return c

cl_putStr :: CLMonad m => String -> m ()
cl_putStr = pluginM . ps_putStr

cl_putStrLn :: CLMonad m => String -> m ()
cl_putStrLn = pluginM . ps_putStrLn

isRunningScript :: MonadState CommandLineState m => m Bool
isRunningScript = liftM isJust $ gets cl_running_script

setRunningScript :: MonadState CommandLineState m => Maybe Script -> m ()
setRunningScript ms = modify $ \st -> st { cl_running_script = ms }

-- TODO: rename?
putStrToConsole :: CLMonad m => String -> m ()
putStrToConsole str = ifM isRunningScript (return ()) (cl_putStrLn str)

------------------------------------------------------------------------------

shellComplete :: (MonadCatch m, MonadIO m, MonadState CommandLineState m) => String -> String -> m [Completion]
shellComplete rPrev so_far = do
    targetQuery <- completionQuery (completionType rPrev)
    -- (liftM.liftM) (map simpleCompletion . nub . filter (so_far `isPrefixOf`))
    --     $ queryS (cl_kernel st) (cl_cursor (cl_session st)) targetQuery
    -- TODO: I expect you want to build a silent version of the kernal_env for this query
    st <- get
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

completionQuery :: (MonadIO m, MonadState CommandLineState m) => CompletionType -> m (TransformH CoreTC [String])
completionQuery ConsiderC       = return $ bindingOfTargetsT       >>^ GHC.varSetToStrings >>^ map ('\'':) >>^ (++ map fst considerables) -- the use of bindingOfTargetsT here is deprecated
completionQuery OccurrenceOfC   = return $ occurrenceOfTargetsT    >>^ GHC.varSetToStrings >>^ map ('\'':)
completionQuery BindingOfC      = return $ bindingOfTargetsT       >>^ GHC.varSetToStrings >>^ map ('\'':)
completionQuery BindingGroupOfC = return $ bindingGroupOfTargetsT  >>^ GHC.varSetToStrings >>^ map ('\'':)
completionQuery RhsOfC          = return $ rhsOfTargetsT           >>^ GHC.varSetToStrings >>^ map ('\'':)
completionQuery InlineC         = return $ promoteT inlineTargetsT >>^                         map ('\'':)
completionQuery CommandC        = get >>= \s -> return $ pure (map externName (cl_externals s))
-- Need to modify opts in completionType function. No key can be a suffix of another key.
completionQuery (AmbiguousC ts) = do
    liftIO $ putStrLn "\nCannot tab complete: ambiguous completion type."
    liftIO $ putStrLn $ "Possibilities: " ++ intercalate ", " (map show ts)
    return (pure [])

------------------------------------------------------------------------------

fixWindow :: CLMonad m => m ()
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

showWindow :: CLMonad m => m ()
showWindow = ifM isRunningScript (return ()) $ fixWindow >> gets cl_window >>= pluginM . display . Just

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
