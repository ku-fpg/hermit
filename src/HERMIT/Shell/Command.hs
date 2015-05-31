{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NoImplicitPrelude #-}
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
    , performTypedEffectH
    , TypedEffectH(..)
    ) where

import Control.Monad.Compat
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.Class (lift)
import Control.Monad.State (get, gets, modify)

import Data.Char
import Data.List.Compat (isPrefixOf, partition)
import Data.Maybe

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

import Prelude.Compat

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
        safeMode = "-safety=strict" `elem` flags
        unsafeMode = "-safety=unsafe" `elem` flags
        safetyMode = if | unsafeMode -> NoSafety
                        | safeMode   -> StrictSafety
                        | otherwise  -> NormalSafety

    modify $ \ st -> st { cl_externals = filterSafety safetyMode $ shell_externals ++ exts
                        , cl_safety = safetyMode
                        }

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
    setRunningScript $ Just [] -- suppress all output until after first scripts run
    sequence_ [ case fileName of
                 "abort"  -> parseScriptCLT "abort" >>= pushScript
                 "resume" -> parseScriptCLT "resume" >>= pushScript
                 _        -> fileToScript fileName >>= pushScript
              | fileName <- reverse filesToLoad
              , not (null fileName)
              ] `catchFailHard` \ msg -> cl_putStrLn $ "Booting Failure: " ++ msg

    let -- Main proof input loop
        loop :: Bool -> InputT m ()
        loop firstInput = do
            ps <- lift $ do tryM () forceProofs
                            getProofStackEmpty
            let prompt = if null ps then "hermit" else "proof"
            mExpr <- lift popScriptLine
            case mExpr of
                Nothing -> do -- no script running
                    when firstInput $ lift $ showWindowAlways Nothing
                    st <- lift get
                    mLine <- if cl_nav st
                             then liftIO getNavCmd
                             else getInputLine $ prompt ++ "<" ++ show (cl_cursor st) ++ "> "

                    case mLine of
                        Nothing          -> lift $ performShellEffect Resume
                        Just ('-':'-':_) -> loop False
                        Just line        -> if all isSpace line
                                            then loop False
                                            else lift (evalScript line `catchFailHard` cl_putStrLn) >> loop False
                Just e -> do
                    lift (runExprH e `catchFailHard` (\ msg -> setRunningScript Nothing >> cl_putStrLn msg))
                    loop True

    -- Start the CLI
    let settings = setComplete (completeWordWithPrev Nothing ws_complete completer) defaultSettings
    runInputT settings (loop True)

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
  [ interpEM $ \ (CrumbBox cr)                  -> setPath (return (mempty @@ cr) :: TransformH LCoreTC LocalPathH)
  , interpEM $ \ (PathBox p)                    -> setPath (return p :: TransformH LCoreTC LocalPathH)
  , interpEM $ \ (StringBox str)                -> performQuery (message str)                           -- QueryH
  , interpEM $ \ (effect :: KernelEffect)       -> flip performKernelEffect effect
  , interpM  $ \ (effect :: ShellEffect)        -> performShellEffect effect                            -- ShellEffectH
  , interpM  $ \ (effect :: ScriptEffect)       -> performScriptEffect effect
  , interpEM $ \ (query :: QueryFun)            -> performQuery query                                   -- QueryH
  , interpEM $ \ (t :: UserProofTechnique)      -> performProofShellCommand $ PCEnd $ UserProof t
  , interpEM $ \ (cmd :: ProofShellCommand)     -> performProofShellCommand cmd
  , interpEM $ \ (TransformLCoreStringBox tt)   -> performQuery (QueryString tt)                        -- QueryH
  , interpEM $ \ (TransformLCoreTCStringBox tt) -> performQuery (QueryString tt)                        -- QueryH
  , interpEM $ \ (TransformLCoreUnitBox tt)     -> performQuery (QueryUnit tt)                          -- QueryH
  , interpEM $ \ (TransformLCoreTCUnitBox tt)   -> performQuery (QueryUnit tt)                          -- QueryH
  , interpEM $ \ (TransformLCorePathBox tt)     -> setPath tt                                           -- SetPathH
  , interpEM $ \ (TransformLCoreTCPathBox tt)   -> setPath tt                                           -- SetPathH
  , interpEM $ \ (TransformLCoreDocHBox t)      -> performQuery (QueryDocH t)                           -- QueryH
  , interpEM $ \ (TransformLCoreTCDocHBox t)    -> performQuery (QueryDocH t)                           -- QueryH
  , interpEM $ \ (RewriteLCoreBox rr)           -> applyRewrite $ promoteLCoreR rr                      -- RewriteLCoreH
  , interpEM $ \ (RewriteLCoreTCBox rr)         -> applyRewrite rr                                      -- RewriteLCoreTCH
  , interpEM $ \ (BiRewriteLCoreBox br)         -> applyRewrite $ promoteLCoreR $ whicheverR br
  , interpEM $ \ (BiRewriteLCoreTCBox br)       -> applyRewrite $ whicheverR br
  , interpEM $ \ (PrettyHLCoreBox t)            -> performQuery (QueryPrettyH t)                        -- QueryH
  , interpEM $ \ (PrettyHLCoreTCBox t)          -> performQuery (QueryPrettyH t)                        -- QueryH
  ]

-------------------------------------------------------------------------------

-- Wish: New Shell entry point
--   * (Wish) This shell returns LocalPathH instead of using setPath. This means *all* the (not Rewrite) Transformations
--     have no effect, and only have a return value.

data TypedEffectH :: * -> * where
  ShellEffectH           :: ShellEffect                         -> TypedEffectH ()
  RewriteLCoreH          :: RewriteH LCore                      -> TypedEffectH ()
  RewriteLCoreTCH        :: RewriteH LCoreTC                    -> TypedEffectH ()
  SetPathH               :: (Injection a LCoreTC) 
                         => TransformH a LocalPathH             -> TypedEffectH ()
  QueryH                 :: QueryFun                            -> TypedEffectH ()
  EvalH                  :: String                              -> TypedEffectH ()

performTypedEffectH :: (MonadCatch m, CLMonad m) => String -> TypedEffectH a -> m a
performTypedEffectH _   (ShellEffectH          effect) = performShellEffect effect 
performTypedEffectH err (RewriteLCoreH         rr    ) = applyRewrite (promoteLCoreR rr) (stubExprH err)
performTypedEffectH err (RewriteLCoreTCH       rr    ) = applyRewrite rr                 (stubExprH err)
performTypedEffectH err (SetPathH              tt    ) = setPath tt                      (stubExprH err)
performTypedEffectH err (QueryH                q     ) = performQuery q                  (stubExprH err)
performTypedEffectH err (EvalH                 e     ) = evalScript e


-- Hacky stub until we replace the ExprH for error messages
stubExprH :: String -> ExprH
stubExprH = SrcName 

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

