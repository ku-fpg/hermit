{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

module HERMIT.Shell.Command
    ( -- * The HERMIT Command-line Shell
      commandLine
    , interpShell
    , unicodeConsole
    , diffDocH
    , diffR
      -- ** Exported for hermit-web
    , performQuery
    , cl_kernel_env
    , getFocusPath
    , evalScript
    ) where

import Control.Monad.State

import Data.Char
import Data.List (isPrefixOf, partition)
import Data.Maybe
import Data.Monoid

import HERMIT.Context
import HERMIT.External
import qualified HERMIT.GHC as GHC
import HERMIT.Kure
import HERMIT.Parser

import HERMIT.Plugin.Renderer

import HERMIT.PrettyPrinter.Common

import HERMIT.Shell.Completion
import HERMIT.Shell.Externals
import HERMIT.Shell.Interpreter
import HERMIT.Shell.KernelEffect
import HERMIT.Shell.Proof
import HERMIT.Shell.ScriptToRewrite
import HERMIT.Shell.ShellEffect
import HERMIT.Shell.Types

#ifdef mingw32_HOST_OS
import HERMIT.Win32.Console
#endif

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

#ifdef mingw32_HOST_OS
cygwinWarning :: String
cygwinWarning = unlines
    [ "WARNING: HERMIT invoked in a Unix-like shell such as Cygwin."
    , "Cygwin does not handle Ctrl-C or tab completion well in some"
    , "Haskell executables. It is recommended that you use a native"
    , "Windows console (such as cmd.exe or PowerShell) instead."
    ]
#endif

-- | The first argument includes a list of files to load.
commandLine :: forall m. (MonadCatch m, MonadException m, CLMonad m)
            => [GHC.CommandLineOption] -> [External] -> m ()
commandLine opts exts = do
    let (flags, filesToLoad) = partition (isPrefixOf "-") opts
        ws_complete = " ()" -- treated as 'whitespace' by completer
        safeMode = "-safe-mode" `elem` flags

    modify $ \ st -> st { cl_externals = shell_externals ++ exts }

    -- Display the banner
    if any (`elem` ["-v0", "-v1"]) flags
        then return ()
        else cl_putStrLn banner

#ifdef mingw32_HOST_OS
    isCyg <- liftIO isCygwinConsole
    if isCyg
        then cl_putStrLn cygwinWarning
        else return ()
#endif

    -- Load and run any scripts
    setRunningScript $ Just []
    sequence_ [ case fileName of
                 "abort"  -> parseScriptCLT "abort" >>= pushScript
                 "resume" -> parseScriptCLT "resume" >>= pushScript
                 _        -> fileToScript fileName >>= pushScript
              | fileName <- reverse filesToLoad
              , not (null fileName)
              ] `catchFailHard` \ msg -> cl_putStrLn $ "Booting Failure: " ++ msg

    let -- Main proof input loop
        loop :: InputT m ()
        loop = do
            el <- lift $ do tryM () announceProven
                            when safeMode $ tryM () forceProofs
                            attemptM currentLemma
            let prompt = either (const "hermit") (const "proof") el
            mExpr <- lift popScriptLine
            case mExpr of
                Nothing -> do -- no script running
                    lift $ ifM isRunningScript (return ()) (showWindow Nothing)
                            `catchFailHard` (cl_putStrLn . ("cannot showWindow: " ++))
                    st <- lift get
                    mLine <- if cl_nav st
                             then liftIO getNavCmd
                             else getInputLine $ prompt ++ "<" ++ show (cl_cursor st) ++ "> "

                    case mLine of
                        Nothing          -> lift $ performShellEffect Resume
                        Just ('-':'-':_) -> loop
                        Just line        -> if all isSpace line
                                            then loop
                                            else lift (evalScript line `catchFailHard` cl_putStrLn) >> loop
                Just e -> lift (runExprH e `catchFailHard` (\ msg -> setRunningScript Nothing >> cl_putStrLn msg)) >> loop

    -- Start the CLI
    let settings = setComplete (completeWordWithPrev Nothing ws_complete completer) defaultSettings
    runInputT settings loop

-- | Like 'catchM', but checks the 'cl_failhard' setting and does so if needed.
catchFailHard :: (MonadCatch m, CLMonad m) => m () -> (String -> m ()) -> m ()
catchFailHard m failure =
    catchM m $ \ msg -> ifM (gets cl_failhard)
                            (do pp <- gets cl_pretty
                                performQuery (QueryPrettyH $ pCoreTC pp) (CmdName "display")
                                cl_putStrLn msg
                                abort)
                            (failure msg)

evalScript :: (MonadCatch m, CLMonad m) => String -> m ()
evalScript = parseScriptCLT >=> mapM_ runExprH

runExprH :: (MonadCatch m, CLMonad m) => ExprH -> m ()
runExprH expr = prefixFailMsg ("Error in expression: " ++ unparseExprH expr ++ "\n") $ do
    ps <- getProofStackEmpty
    (if null ps then id else withProofExternals) $ interpExprH interpShell expr

-- | Interpret a boxed thing as one of the four possible shell command types.
interpShell :: (MonadCatch m, CLMonad m) => [Interp m ()]
interpShell =
  [ interpEM $ \ (RewriteCoreBox rr)           -> applyRewrite $ promoteCoreR rr
  , interpEM $ \ (RewriteCoreTCBox rr)         -> applyRewrite $ promoteCoreTCR rr
  , interpEM $ \ (BiRewriteCoreBox br)         -> applyRewrite $ promoteCoreR $ whicheverR br
  , interpEM $ \ (CrumbBox cr)                 -> setPath (return (mempty @@ cr) :: TransformH QC LocalPathH)
  , interpEM $ \ (PathBox p)                   -> setPath (return p :: TransformH QC LocalPathH)
  , interpEM $ \ (TransformCorePathBox tt)     -> setPath tt
  , interpEM $ \ (TransformCoreTCPathBox tt)   -> setPath tt
  , interpEM $ \ (TransformQCLocalPathBox tt)  -> setPath tt
  , interpEM $ \ (StringBox str)               -> performQuery (message str)
  , interpEM $ \ (TransformCoreStringBox tt)   -> performQuery (QueryString tt)
  , interpEM $ \ (TransformCoreTCStringBox tt) -> performQuery (QueryString tt)
  , interpEM $ \ (TransformCoreDocHBox t)      -> performQuery (QueryDocH t)
  , interpEM $ \ (TransformCoreTCDocHBox t)    -> performQuery (QueryDocH t)
  , interpEM $ \ (PrettyHCoreBox t)            -> performQuery (QueryPrettyH t)
  , interpEM $ \ (PrettyHCoreTCBox t)          -> performQuery (QueryPrettyH t)
  , interpEM $ \ (TransformCoreCheckBox tt)    -> performQuery (QueryUnit tt)
  , interpEM $ \ (TransformCoreTCCheckBox tt)  -> performQuery (QueryUnit tt)
  , interpEM $ \ (effect :: KernelEffect)      -> flip performKernelEffect effect
  , interpM  $ \ (effect :: ShellEffect)       -> performShellEffect effect
  , interpM  $ \ (effect :: ScriptEffect)      -> performScriptEffect effect
  , interpEM $ \ (query :: QueryFun)           -> performQuery query
  , interpEM $ \ (t :: UserProofTechnique)     -> performProofShellCommand $ PCUser t
  , interpEM $ \ (cmd :: ProofShellCommand)    -> performProofShellCommand cmd
  , interpEM $ \ (RewriteQCBox r)              -> applyRewrite r
  , interpEM $ \ (TransformQCStringBox t)      -> performQuery (QueryString t)
  , interpEM $ \ (TransformQCUnitBox t)        -> performQuery (QueryUnit t)
  ]

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

