{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
module HERMIT.Shell.Types where

import Control.Applicative
import Control.Arrow
import Control.Concurrent.STM
import Control.Monad (liftM, unless)
import Control.Monad.Error.Class (MonadError(..))
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.State (MonadState(..), StateT(..), gets, modify)
import Control.Monad.Trans.Class (MonadTrans(..))
import Control.Monad.Trans.Except (ExceptT(..), runExceptT)

import Data.Dynamic
import qualified Data.Map as M
import Data.Maybe (fromJust, fromMaybe, isJust)
import Data.Monoid (mempty)

import HERMIT.Context
import HERMIT.Core
import HERMIT.Dictionary.Reasoning hiding (externals)
import HERMIT.External
import qualified HERMIT.GHC as GHC
import HERMIT.Kernel
import HERMIT.Kure
import HERMIT.Lemma
import HERMIT.Parser
import HERMIT.PrettyPrinter.Common
import HERMIT.Syntax

import HERMIT.Plugin.Display
import HERMIT.Plugin.Renderer
import HERMIT.Plugin.Types

import System.Console.Haskeline hiding (catch, display)
import System.IO (Handle, stdout)

#ifdef mingw32_HOST_OS
import HERMIT.Win32.Console
#else
import System.Console.Terminfo (setupTermFromEnv, getCapability, termColumns, termLines)
#endif

----------------------------------------------------------------------------------

data QueryFun :: * where
   QueryString         :: (Injection GHC.ModGuts g, Walker HermitC g)
                       => TransformH g String                         -> QueryFun
   QueryDocH           :: (Injection GHC.ModGuts g, Walker HermitC g)
                       => TransformH g DocH                           -> QueryFun
   QueryPrettyH        :: (Injection GHC.ModGuts g, Walker HermitC g)
                       => PrettyH g                                   -> QueryFun
   Diff                :: AST -> AST                                  -> QueryFun
   Inquiry             :: (CommandLineState -> IO String)             -> QueryFun
   CorrectnessCriteria :: (Injection GHC.ModGuts g, Walker HermitC g)
                       => TransformH g ()                             -> QueryFun
   deriving Typeable

message :: String -> QueryFun
message str = Inquiry (const $ return str)

instance Extern QueryFun where
   type Box QueryFun = QueryFun
   box i = i
   unbox i = i

performQuery :: (MonadCatch m, CLMonad m) => QueryFun -> ExprH -> m ()
performQuery qf expr = go qf
    where expr' = Just $ unparseExprH expr
          go (QueryString q) =
            putStrToConsole =<< prefixFailMsg "Query failed: " (queryInFocus q expr')

          go (QueryDocH q) = do
            doc <- prefixFailMsg "Query failed: " $ queryInFocus q expr'
            st <- get
            liftIO $ cl_render st stdout (cl_pretty_opts st) (Right doc)

          go (QueryPrettyH q) = do
            st <- get
            doc <- prefixFailMsg "Query failed: " $ queryInFocus (liftPrettyH (pOptions (cl_pretty st)) q) expr'
            liftIO $ cl_render st stdout (cl_pretty_opts st) (Right doc)

          go (Inquiry f) = get >>= liftIO . f >>= putStrToConsole

          go (Diff ast1 ast2) = do
            st <- get
            all_asts <- listK (cl_kernel st)

            let getCmds ast
                    | ast == ast1 = []
                    | otherwise   = case [ (p,msg) | (to,msg,Just p) <- all_asts, to == ast ] of
                                            [(ast',msg)] -> fromMaybe "-- unknown command!" msg : getCmds ast'
                                            _ -> ["error: history broken!"] -- should be impossible

            cl_putStrLn "Commands:"
            cl_putStrLn "========="
            cl_putStrLn $ unlines $ reverse $ getCmds ast2

            doc1 <- ppWholeProgram ast1
            doc2 <- ppWholeProgram ast2

            r <- diffDocH (cl_pretty st) doc1 doc2

            cl_putStrLn "Diff:"
            cl_putStrLn "====="
            cl_putStr r

          go (CorrectnessCriteria q) = do
            -- TODO: Again, we may want a quiet version of the kernel_env
            let str = fromJust expr'
            modFailMsg (\ err -> str ++ " [exception: " ++ err ++ "]") $ queryInFocus q expr'
            putStrToConsole $ str ++ " [correct]"

ppWholeProgram :: (CLMonad m, MonadCatch m) => AST -> m DocH
ppWholeProgram ast = do
    st <- get
    d <- queryK (cl_kernel st)
                (extractT $ pathT [ModGuts_Prog] $ liftPrettyH (cl_pretty_opts st) $ pCoreTC $ cl_pretty st)
                Nothing
                (cl_kernel_env st) ast
    return $ snd d -- discard new AST, assuming pp won't create one

----------------------------------------------------------------------------------

type TagName = String
data VersionCmd = Back            -- back (up) the derivation tree
                | Step            -- down one step; assumes only one choice
                | Goto AST        -- goto a specific AST
                | GotoTag TagName -- goto a specific AST, by tag name
                | Tag TagName     -- tag the current AST with a name
        deriving Show

----------------------------------------------------------------------------------

data CLException = CLAbort
                 | CLResume AST
                 | CLContinue CommandLineState -- TODO: needed?
                 | CLError String

abort :: MonadError CLException m => m a
abort = throwError CLAbort

resume :: MonadError CLException m => AST -> m a
resume = throwError . CLResume

continue :: MonadError CLException m => CommandLineState -> m a
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
newtype CLT m a = CLT { unCLT :: ExceptT CLException (StateT CommandLineState m) a }
    deriving (Functor, Applicative, MonadIO, MonadError CLException, MonadState CommandLineState)

-- Adapted from System.Console.Haskeline.MonadException, which hasn't provided an instance for ExceptT yet
instance MonadException m => MonadException (ExceptT e m) where
    controlIO f = ExceptT $ controlIO $ \(RunIO run) -> let
                    run' = RunIO (fmap ExceptT . run . runExceptT)
                    in fmap runExceptT $ f run'

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
runCLT s = flip runStateT s . runExceptT . unCLT

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

-- Session-local issues; things that are never saved (except the PluginState).
data CommandLineState = CommandLineState
    { cl_pstate         :: PluginState            -- ^ Access to the enclosing plugin state. This is propagated back
                                                  --   to the plugin after the CLT computation ends. We do it this way
                                                  --   because nested StateT is a pain.
    , cl_height         :: Int                    -- ^ console height, in lines
    , cl_scripts        :: [(ScriptName,Script)]
    , cl_nav            :: Bool                   -- ^ keyboard input the nav panel
    , cl_foci           :: M.Map AST ([LocalPathH], LocalPathH) -- ^ focus assigned to each AST
    , cl_tags           :: M.Map AST [String]     -- ^ list of tags on an AST
    , cl_proofstack     :: M.Map AST [ProofTodo]  -- ^ stack of todos for the proof shell
    , cl_window         :: PathH                  -- ^ path to beginning of window, always a prefix of focus path in kernel
    , cl_externals      :: [External]             -- ^ Currently visible externals
    , cl_running_script :: Maybe Script           -- ^ Nothing = no script running, otherwise the remaining script commands
    } deriving (Typeable)

data ProofTodo = Unproven LemmaName Lemma [NamedLemma] Bool -- ^ lemma we are proving, plus temporary lemmas in scope
               | Proven LemmaName                      Bool -- ^ lemma successfully proven, temporary status

-- To ease the pain of nested records, define some boilerplate here.
cl_corelint :: CommandLineState -> Bool
cl_corelint = ps_corelint . cl_pstate

setCoreLint :: CommandLineState -> Bool -> CommandLineState
setCoreLint st b = st { cl_pstate = (cl_pstate st) { ps_corelint = b } }

cl_cursor :: CommandLineState -> AST
cl_cursor = ps_cursor . cl_pstate

setCursor :: AST -> CommandLineState -> CommandLineState
setCursor sast st = st { cl_pstate = (cl_pstate st) { ps_cursor = sast } }

cl_diffonly :: CommandLineState -> Bool
cl_diffonly = ps_diffonly . cl_pstate

setDiffOnly :: CommandLineState -> Bool -> CommandLineState
setDiffOnly st b = st { cl_pstate = (cl_pstate st) { ps_diffonly = b } }

cl_failhard :: CommandLineState -> Bool
cl_failhard = ps_failhard . cl_pstate

setFailHard :: CommandLineState -> Bool -> CommandLineState
setFailHard st b = st { cl_pstate = (cl_pstate st) { ps_failhard = b } }

cl_kernel :: CommandLineState -> Kernel
cl_kernel = ps_kernel . cl_pstate

cl_kernel_env :: CommandLineState -> KernelEnv
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
                              , cl_nav            = False
                              , cl_foci           = M.empty
                              , cl_tags           = M.empty
                              , cl_proofstack     = M.empty
                              , cl_window         = mempty
                              , cl_externals      = [] -- Note, empty dictionary.
                              , cl_running_script = Nothing
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

pathStack2Paths :: [LocalPath crumb] -> LocalPath crumb -> [Path crumb]
pathStack2Paths ps p = reverse (map snocPathToPath (p:ps))

-- | A primitive means of denoting navigation of a tree (within a local scope).
data Direction = L -- ^ Left
               | R -- ^ Right
               | U -- ^ Up
               | T -- ^ Top
               deriving (Eq,Show)

-- | Movement confined within the local scope.
moveLocally :: Direction -> LocalPathH -> LocalPathH
moveLocally d (SnocPath p) = case p of
                               []     -> mempty
                               cr:crs -> case d of
                                           T -> mempty
                                           U -> SnocPath crs
                                           L -> SnocPath (fromMaybe cr (leftSibling cr)  : crs)
                                           R -> SnocPath (fromMaybe cr (rightSibling cr) : crs)


pathStackToLens :: (Injection a g, Walker HermitC g) => [LocalPathH] -> LocalPathH -> LensH a g
pathStackToLens ps p = injectL >>> pathL (concat $ pathStack2Paths ps p)

-- This function is used to check the validity of paths, so which sum type we use is important.
testPathStackT :: [LocalPathH] -> LocalPathH -> TransformH GHC.ModGuts Bool
testPathStackT ps p = testLensT (pathStackToLens ps p :: LensH GHC.ModGuts CoreTC)

getPathStack :: CLMonad m => m ([LocalPathH], LocalPathH)
getPathStack = do
    st <- get
    return $ fromMaybe ([],mempty) (M.lookup (cl_cursor st) (cl_foci st))

getFocusPath :: CLMonad m => m PathH
getFocusPath = do
    (base, rel) <- getPathStack
    return $ concat $ pathStack2Paths base rel

addFocusT :: (Injection a g, Walker HermitC g, CLMonad m) => TransformH g b -> m (TransformH a b)
addFocusT t = do
    (base, rel) <- getPathStack
    return $ focusT (pathStackToLens base rel) t

addFocusR :: (Injection a g, Walker HermitC g, CLMonad m) => RewriteH g -> m (RewriteH a)
addFocusR r = do
    (base, rel) <- getPathStack
    return $ focusR (pathStackToLens base rel) r

------------------------------------------------------------------------------

addAST :: CLMonad m => AST -> m ()
addAST ast = addASTWithPath ast id

addASTWithPath :: CLMonad m => AST -> (LocalPathH -> LocalPathH) -> m ()
addASTWithPath ast f = do
    (base, rel) <- getPathStack
    copyProofStack ast
    modify $ \ st -> setCursor ast (st { cl_foci = M.insert ast (base, f rel) (cl_foci st) })

copyProofStack :: CLMonad m => AST -> m ()
copyProofStack ast = modify $ \ st -> let newStack = fromMaybe [] $ M.lookup (cl_cursor st) (cl_proofstack st)
                                      in st { cl_proofstack = M.insert ast newStack (cl_proofstack st) }

pushProofStack :: CLMonad m => ProofTodo -> m ()
pushProofStack todo = modify $ \ st -> st { cl_proofstack = M.insertWith (++) (cl_cursor st) [todo] (cl_proofstack st) }

popProofStack :: CLMonad m => m ProofTodo
popProofStack = do
    t : ts <- getProofStack
    modify $ \ st -> st { cl_proofstack = M.insert (cl_cursor st) ts (cl_proofstack st) }
    return t

currentLemma :: CLMonad m => m (LemmaName, Lemma, [NamedLemma])
currentLemma = do
    todo : _ <- getProofStack

    case todo of
        Unproven nm l ls _ -> return (nm, l, ls)
        Proven _ _ -> fail "currentLemma: Proven lemma on top of stack!"

announceProven :: (MonadCatch m, CLMonad m) => m ()
announceProven = getProofStack >>= go
    where go (Proven nm temp : r) = do
            queryInFocus (unless temp (modifyLemmaT nm id idR (const True) id) :: TransformH Core ())
                         (Just $ "-- proven " ++ quoteShow nm) -- comment in script
            -- take it off the stack for the new AST
            modify $ \ st -> st { cl_proofstack = M.insert (cl_cursor st) r (cl_proofstack st) }
            cl_putStrLn ("Successfully proven: " ++ show nm) >> go r
          go _ = return ()

-- | Always returns a non-empty list.
getProofStack :: CLMonad m => m [ProofTodo]
getProofStack = do
    (ps, ast) <- gets (cl_proofstack &&& cl_cursor)

    case M.lookup ast ps of
        Just todos@(_:_) -> return todos
        _ -> fail "No lemma currently being proved."

------------------------------------------------------------------------------

fixWindow :: CLMonad m => m ()
fixWindow = do
    -- check to make sure new path is still inside window
    focusPath <- getFocusPath
    -- move the window in two cases:
    --  1. window path is not prefix of focus path
    --  2. window path is empty (since at the top level we only show type sigs)
    {- when (not (isPrefixOf (cl_window st) focusPath) || null (cl_window st))
       $ put $ st { cl_window = focusPath } -}
    modify $ \ st -> st { cl_window = focusPath  } -- TODO: temporary until we figure out a better highlight interface

showWindow :: CLMonad m => m ()
showWindow = ifM isRunningScript (return ()) $ fixWindow >> gets cl_window >>= pluginM . display . Just

------------------------------------------------------------------------------

queryInFocus :: (Walker HermitC g, Injection GHC.ModGuts g, MonadCatch m, CLMonad m)
             => TransformH g b -> Maybe String -> m b
queryInFocus t msg = do
    q <- addFocusT t
    st <- get
    (ast', r) <- queryK (cl_kernel st) q msg (cl_kernel_env st) (cl_cursor st)
    addAST ast'
    return r

