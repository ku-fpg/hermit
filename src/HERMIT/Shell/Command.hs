{-# LANGUAGE LambdaCase, ScopedTypeVariables, GADTs, FlexibleContexts, TypeFamilies #-}

module HERMIT.Shell.Command
    ( -- * The HERMIT Command-line Shell
      commandLine
    , unicodeConsole
    , diffDocH
    , diffR
      -- ** Exported for hermit-web
    , performQuery
    , cl_kernel_env
    , getFocusPath
    , shellComplete
    , evalScript
    ) where

import Control.Concurrent
import Control.Monad.State
import Control.Monad.Error

import Data.Char
import Data.List (isPrefixOf, partition)
import Data.Maybe

import HERMIT.External
import qualified HERMIT.GHC as GHC
import HERMIT.Kernel.Scoped hiding (abortS, resumeS)
import HERMIT.Kure
import HERMIT.Parser

import HERMIT.Plugin.Display
import HERMIT.Plugin.Renderer

import HERMIT.Shell.Dictionary
import HERMIT.Shell.Externals
import HERMIT.Shell.Interpreter
import HERMIT.Shell.KernelEffect
import HERMIT.Shell.Proof
import HERMIT.Shell.ScriptToRewrite
import HERMIT.Shell.ShellEffect
import HERMIT.Shell.Types

import System.IO

-- import System.Console.ANSI
import System.Console.Haskeline hiding (catch, display)

-------------------------------------------------------------------------------

banner :: String
banner = unlines
    [ "===================== Welcome to HERMIT ======================"
    , "HERMIT is a toolkit for the interactive transformation of GHC"
    , "core language programs. Documentation on HERMIT can be found"
    , "on the HERMIT web page at:"
    , "http://www.ittc.ku.edu/csdl/fpg/software/hermit.html"
    , ""
    , "You have just loaded the interactive shell. To exit, type "
    , "\"abort\" or \"resume\" to abort or resume GHC compilation."
    , ""
    , "Type \"help\" for instructions on how to list or search the"
    , "available HERMIT commands."
    , ""
    , "To get started, you could try the following:"
    , "  - type \"binding-of 'foo\", where \"foo\" is a function"
    , "    defined in the module;"
    , "  - type \"set-pp-type Show\" to display full type information;"
    , "  - type \"info\" for more information about the current node;"
    , "  - to descend into a child node, type the name of the child"
    , "    (\"info\" includes a list of children of the current node);"
    , "  - to ascend, use the \"up\" command;"
    , "  - type \"log\" to display an activity log."
    , "=============================================================="
    ]

-- | The first argument includes a list of files to load.
commandLine :: [GHC.CommandLineOption] -> Behavior -> [External] -> CLT IO ()
commandLine opts behavior exts = do
    let (flags, filesToLoad) = partition (isPrefixOf "-") opts
        ws_complete = " ()"

    modify $ \ st -> st { cl_dict = mkDict (shell_externals ++ exts) }

    clState <- get
    completionMVar <- liftIO $ newMVar clState

    let loop :: CLT (InputT IO) ()
        loop = do
            st <- get
            let SAST n = cl_cursor st
            mLine <- if cl_nav st
                     then liftIO getNavCmd
                     else do liftIO $ modifyMVar_ completionMVar (const $ return st) -- so the completion can get the current state
                             lift $ getInputLine $ "hermit<" ++ show n ++ "> "

            case mLine of
                Nothing          -> performShellEffect Resume
                Just ('-':'-':_) -> loop
                Just line        -> if all isSpace line
                                    then loop
                                    else (evalScript line `catchFailHard` cl_putStrLn) >> loop

    -- Display the banner
    if any (`elem` ["-v0", "-v1"]) flags
        then return ()
        else cl_putStrLn banner

    -- Load and run any scripts
    setRunningScript $ Just []
    sequence_ [ case fileName of
                 "abort"  -> performShellEffect Abort
                 "resume" -> performShellEffect Resume
                 _        -> performScriptEffect runExprH $ loadAndRun fileName
              | fileName <- reverse filesToLoad
              , not (null fileName)
              ] `catchFailHard` \ msg -> cl_putStrLn $ "Booting Failure: " ++ msg
    setRunningScript Nothing

    -- Start the CLI
    showWindow
    let settings = setComplete (completeWordWithPrev Nothing ws_complete (shellComplete completionMVar)) defaultSettings
    (r,s) <- get >>= liftIO . runInputTBehavior behavior settings . flip runCLT loop
    either throwError (\v -> put s >> return v) r

-- | Like 'catchM', but checks the 'cl_failhard' setting and does so if needed.
catchFailHard :: MonadIO m => CLT m () -> (String -> CLT m ()) -> CLT m ()
catchFailHard m failure = catchM m $ \ msg -> ifM (gets cl_failhard) (performQuery Display (CmdName "display") >> cl_putStrLn msg >> abort) (failure msg)

evalScript :: (MonadCatch m, MonadError CLException m, MonadIO m, MonadState CommandLineState m) => String -> m ()
evalScript = parseScriptCLT >=> mapM_ runExprH

runExprH :: (MonadCatch m, MonadError CLException m, MonadIO m, MonadState CommandLineState m) => ExprH -> m ()
runExprH expr = prefixFailMsg ("Error in expression: " ++ unparseExprH expr ++ "\n") $ do
    shellCmd <- interpExprH interpShellCommand expr
    case shellCmd of
        KernelEffect effect -> performKernelEffect effect expr
        ScriptEffect effect -> performScriptEffect runExprH effect
        ShellEffect effect  -> performShellEffect effect
        QueryFun query      -> performQuery query expr
        ProofCommand cmd    -> performProofCommand cmd

-------------------------------------------------------------------------------

-- TODO: This can be refactored. We always showWindow. Also, Perhaps return a modifier, not ()
--   UPDATE: Not true.  We don't always showWindow.
-- TODO: All of these should through an exception if they fail to execute the command as given.

-------------------------------------------------------------------------------

getNavCmd :: IO (Maybe String)
getNavCmd = do
        b_in <- hGetBuffering stdin
        hSetBuffering stdin NoBuffering
        b_out <- hGetBuffering stdin
        hSetBuffering stdout NoBuffering
        ec_in <- hGetEcho stdin
        hSetEcho stdin False
        putStr "(navigation mode; use arrow keys, escape to quit, '?' for help)"
        r <- readCh []
        putStr "\n"
        hSetBuffering stdin b_in
        hSetBuffering stdout b_out
        hSetEcho stdin ec_in
        return r
  where
   readCh xs = do
        x <- getChar
        let str = xs ++ [x]
        (fromMaybe reset $ lookup str cmds) str

   reset _ = do
        putStr "\BEL"
        readCh []

   res str _ = return (Just str)

   cmds = [ ("\ESC" , \ str -> ifM (hReady stdin)
                                   (readCh str)
                                   (return $ Just "command-line"))
          , ("\ESC[" , readCh)
          , ("\ESC[A", res "up")
          , ("\ESC[B", res "down")
          , ("\ESC[C", res "right")
          , ("\ESC[D", res "left")
          , ("?",      res "nav-commands")
          , ("f",      res "step")
          ] ++
          [ (show n, res (show n)) | n <- [0..9] :: [Int] ]

