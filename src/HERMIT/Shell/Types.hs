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

-- There are 4 types of commands, AST effect-ful, Shell effect-ful, Queries, and Meta-commands.

data ShellCommand =  AstEffect   AstEffect
                  |  ShellEffect ShellEffect
                  |  QueryFun    QueryFun
                  |  MetaCommand MetaCommand

-- GADTs can't have docs on constructors. See Haddock ticket #43.
-- | AstEffects are things that are recorded in our log and saved files.
--   - Apply a rewrite (giving a whole new lower-level AST).
--   - Change the current location using a computed path.
--   - Change the currect location using directions.
--   - Begin or end a scope.
--   - Add a tag.
--   - Run a precondition or other predicate that must not fail.
data AstEffect :: * where
   Apply      :: (Injection GHC.ModGuts g, Walker HermitC g) => RewriteH g              -> AstEffect
   Pathfinder :: (Injection GHC.ModGuts g, Walker HermitC g) => TranslateH g LocalPathH -> AstEffect
   Direction  ::                                                Direction               -> AstEffect
--   PushFocus Path -- This changes the current location using a give path
   BeginScope ::                                                                           AstEffect
   EndScope   ::                                                                           AstEffect
   Tag        :: String                                                                 -> AstEffect
   CorrectnessCritera :: (Injection GHC.ModGuts g, Walker HermitC g) => TranslateH g () -> AstEffect
   deriving Typeable

instance Extern AstEffect where
   type Box AstEffect = AstEffect
   box i = i
   unbox i = i

data ShellEffect :: * where
   CLSModify :: (CommandLineState -> IO CommandLineState) -> ShellEffect
   deriving Typeable

data QueryFun :: * where
   QueryString   :: (Injection GHC.ModGuts g, Walker HermitC g) => TranslateH g String                             -> QueryFun
   QueryDocH     ::                                     (PrettyC -> PrettyH CoreTC -> TranslateH CoreTC DocH)      -> QueryFun
   -- These two be can generalized into
   --  (CommandLineState -> IO String)
   Display       ::                                                                                                   QueryFun
--   Message       ::                                                String                                          -> QueryFun
   Inquiry       ::                                                (CommandLineState -> IO String) -> QueryFun
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
   | Dump String String String Int
   | LoadFile ScriptName FilePath  -- load a file on top of the current node
   | SaveFile FilePath
   | ScriptToRewrite ScriptName
   | DefineScript ScriptName String
   | RunScript ScriptName
   | SaveScript FilePath ScriptName
   | Delete SAST
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

-- TODO: Use another word, Navigation is a more general concept
-- Perhaps VersionNavigation
data Navigation = Back                  -- back (up) the derivation tree
                | Step                  -- down one step; assumes only one choice
                | Goto Int              -- goto a specific node, if possible
                | GotoTag String        -- goto a specific named tag
        deriving Show

data ShellCommandBox = ShellCommandBox ShellCommand deriving Typeable

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
type Script = [ExprH]
