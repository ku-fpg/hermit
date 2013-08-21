{-# LANGUAGE KindSignatures, GADTs, FlexibleContexts, TypeFamilies, DeriveDataTypeable #-}

module HERMIT.Shell.Types where

import qualified GhcPlugins as GHC

import Control.Concurrent.STM
import Control.Monad.State
import Control.Monad.Error

import Data.Dynamic
import qualified Data.Map as M

import HERMIT.Context
import HERMIT.Kure
import HERMIT.Dictionary
import HERMIT.External
import HERMIT.Kernel.Scoped
import HERMIT.Parser
import HERMIT.PrettyPrinter.Common

import System.IO

----------------------------------------------------------------------------------

-- | There are four types of commands.
data ShellCommand =  KernelEffect KernelEffect -- ^ Command that modifies the state of the (scoped) kernel.
                  |  ShellEffect  ShellEffect  -- ^ Command that modifies the state of the shell.
                  |  QueryFun     QueryFun     -- ^ Command that queries the AST with a Translate (read only).
                  |  MetaCommand  MetaCommand  -- ^ Command that otherwise controls HERMIT (abort, resume, save, etc).

-- GADTs can't have docs on constructors. See Haddock ticket #43.
-- | KernelEffects are things that affect the state of the Kernel
--   - Apply a rewrite (giving a whole new lower-level AST).
--   - Change the current location using a computed path.
--   - Change the currect location using directions.
--   - Begin or end a scope.
--   - Run a precondition or other predicate that must not fail.
data KernelEffect :: * where
   Apply      :: (Injection GHC.ModGuts g, Walker HermitC g) => RewriteH g              -> KernelEffect
   Pathfinder :: (Injection GHC.ModGuts g, Walker HermitC g) => TranslateH g LocalPathH -> KernelEffect
   Direction  ::                                                Direction               -> KernelEffect
   BeginScope ::                                                                           KernelEffect
   EndScope   ::                                                                           KernelEffect
   CorrectnessCritera :: (Injection GHC.ModGuts g, Walker HermitC g) => TranslateH g () -> KernelEffect
   deriving Typeable

instance Extern KernelEffect where
   type Box KernelEffect = KernelEffect
   box i = i
   unbox i = i

data ShellEffect :: * where
   CLSModify :: (CommandLineState -> IO CommandLineState) -> ShellEffect
   deriving Typeable

data QueryFun :: * where
   QueryString   :: (Injection GHC.ModGuts g, Walker HermitC g)
                 => TranslateH g String                                   -> QueryFun
   QueryDocH     :: (PrettyC -> PrettyH CoreTC -> TranslateH CoreTC DocH) -> QueryFun
   Display       ::                                                          QueryFun
   Inquiry       :: (CommandLineState -> IO String)                       -> QueryFun
   deriving Typeable

message :: String -> QueryFun
message str = Inquiry (const $ return str)

instance Extern QueryFun where
   type Box QueryFun = QueryFun
   box i = i
   unbox i = i

data MetaCommand
   = Resume
   | Abort
   | Delete SAST
   | Dump String String String Int
   | LoadFile ScriptName FilePath  -- load a file on top of the current node
   | SaveFile FilePath
   | ScriptToRewrite ScriptName
   | DefineScript ScriptName String
   | RunScript ScriptName
   | SaveScript FilePath ScriptName
   | SeqMeta [MetaCommand]
   deriving Typeable

-- | A composite meta-command for running a loaded script immediately.
--   The script is given the same name as the filepath.
loadAndRun :: FilePath -> MetaCommand
loadAndRun fp = SeqMeta [LoadFile fp fp, RunScript fp]

instance Extern MetaCommand where
    type Box MetaCommand = MetaCommand
    box i = i
    unbox i = i

data VersionCmd = Back                  -- back (up) the derivation tree
                | Step                  -- down one step; assumes only one choice
                | Goto Int              -- goto a specific node, if possible
                | GotoTag String        -- goto a specific named tag
                | AddTag String         -- add a tag
        deriving Show

instance Extern ShellEffect where
    type Box ShellEffect = ShellEffect
    box i = i
    unbox i = i

----------------------------------------------------------------------------------

type CLM m a = ErrorT String (StateT CommandLineState m) a

-- TODO: Come up with names for these, and/or better characterise these abstractions.
iokm2clm' :: MonadIO m => String -> (a -> CLM m b) -> IO (KureM a) -> CLM m b
iokm2clm' msg ret m = liftIO m >>= runKureM ret (throwError . (msg ++))

iokm2clm :: MonadIO m => String -> IO (KureM a) -> CLM m a
iokm2clm msg = iokm2clm' msg return

iokm2clm'' :: MonadIO m => IO (KureM a) -> CLM m a
iokm2clm'' = iokm2clm ""

data VersionStore = VersionStore
    { vs_graph       :: [(SAST,ExprH,SAST)]
    , vs_tags        :: [(String,SAST)]
    }

newSAST :: ExprH -> SAST -> CommandLineState -> CommandLineState
newSAST expr sast st = st { cl_cursor = sast
                          , cl_version = (cl_version st) { vs_graph = (cl_cursor st, expr, sast) : vs_graph (cl_version st) }
                          }

-- Session-local issues; things that are never saved.
data CommandLineState = CommandLineState
    { cl_cursor         :: SAST                                     -- ^ the current AST
    , cl_pretty         :: String                                   -- ^ which pretty printer to use
    , cl_pretty_opts    :: PrettyOptions                            -- ^ the options for the pretty printer
    , cl_render         :: Handle -> PrettyOptions -> DocH -> IO () -- ^ the way of outputing to the screen
    , cl_height         :: Int                                      -- ^ console height, in lines
    , cl_nav            :: Bool                                     -- ^ keyboard input the nav panel
    , cl_running_script :: Bool                                     -- ^ if running a script
    , cl_tick           :: TVar (M.Map String Int)                  -- ^ the list of ticked messages
    , cl_corelint       :: Bool                                     -- ^ if true, run Core Lint on module after each rewrite
    , cl_failhard       :: Bool                                     -- ^ if true, abort on *any* failure
    , cl_window         :: PathH                                    -- ^ path to beginning of window, always a prefix of focus path in kernel
    -- these four should be in a reader
    , cl_dict           :: Dictionary
    , cl_scripts        :: [(ScriptName,Script)]
    , cl_kernel         :: ScopedKernel
    , cl_initSAST       :: SAST
    -- and the version store
    , cl_version        :: VersionStore
    }

type ScriptName = String
