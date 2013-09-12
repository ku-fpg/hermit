{-# LANGUAGE LambdaCase, ScopedTypeVariables, GADTs #-}

module HERMIT.Shell.Command
    ( -- * The HERMIT Command-line Shell
      commandLine
    , unicodeConsole
      -- ** Exported for hermit-web
    , performKernelEffect
    , performQuery
    , performShellEffect
    , performMetaCommand
    , cl_kernel_env
    , getFocusPath
    , shellComplete
    , evalScript
    ) where

import Control.Applicative
import Control.Arrow hiding (loop)
import Control.Concurrent
import Control.Concurrent.STM
import Control.Exception.Base hiding (catch)
import Control.Monad.State
import Control.Monad.Error

import Data.Char
import Data.Monoid
import Data.List (intercalate, isPrefixOf, nub, partition)
import qualified Data.Map as M
import Data.Maybe

import HERMIT.Monad
import HERMIT.Kure
import HERMIT.Dictionary
import HERMIT.External
import qualified HERMIT.GHC as GHC
import HERMIT.Interp
import HERMIT.Kernel (queryK)
import HERMIT.Kernel.Scoped hiding (abortS, resumeS)
import HERMIT.Parser
import HERMIT.PrettyPrinter.Common

import HERMIT.Primitive.GHC
import HERMIT.Primitive.Inline
import HERMIT.Primitive.Navigation

import HERMIT.Shell.Externals
import HERMIT.Shell.ScriptToRewrite
import HERMIT.Shell.Renderer
import HERMIT.Shell.Types

import System.IO

-- import System.Console.ANSI
import System.Console.Haskeline hiding (catch)
import System.Console.Terminfo (setupTermFromEnv, getCapability, termColumns, termLines)

----------------------------------------------------------------------------------

catch :: IO a -> (String -> IO a) -> IO a
catch = catchJust (\ (err :: IOException) -> return (show err))

cl_putStr :: MonadIO m => String -> CLM m ()
cl_putStr str = do
    st <- get
    liftIO $ cl_render st stdout (cl_pretty_opts st) (Left str)

cl_putStrLn :: MonadIO m => String -> CLM m ()
cl_putStrLn = cl_putStr . (++"\n")

fixWindow :: MonadIO m => CLM m ()
fixWindow = do
    st <- get
    -- check to make sure new path is still inside window
    focusPath <- getFocusPath
    -- move the window in two cases:
    --  1. window path is not prefix of focus path
    --  2. window path is empty (since at the top level we only show type sigs)
    {- when (not (isPrefixOf (cl_window st) focusPath) || null (cl_window st))
       $ put $ st { cl_window = focusPath } -}
    put $ st { cl_window = focusPath } -- TODO: temporary until we figure out a better highlight interface

getFocusPath :: MonadIO m => CLM m PathH
getFocusPath = get >>= \ st -> liftM concat $ prefixFailMsg "getFocusPath - pathS failed: " $ pathS (cl_kernel st) (cl_cursor st)

showWindow :: MonadIO m => CLM m ()
showWindow = do
    fixWindow
    st <- get
    focusPath <- getFocusPath
    let skernel = cl_kernel st
        ppOpts = (cl_pretty_opts st) { po_focus = Just focusPath }
    -- No not show focus while loading
    ifM (gets cl_running_script)
        (return ())
        (iokm2clm' "Rendering error: "
                   (liftIO . cl_render st stdout ppOpts . Right)
                   (toASTS skernel (cl_cursor st) >>= \ ast ->
                        queryK (kernelS skernel) ast (extractT $ pathT (cl_window st) $ liftPrettyH ppOpts $ cl_pretty st) (cl_kernel_env st))
        )

-------------------------------------------------------------------------------

data CompletionType = ConsiderC -- complete with possible arguments to consider
                    | InlineC   -- complete with names that can be inlined
                    | CommandC  -- complete using dictionary commands (default)
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
          opts = [ ("inline"  , InlineC  )
                 , ("consider", ConsiderC)
                 , ("rhs-of"  , ConsiderC)
                 ]

-- TODO: For the moment, we promote the translations on Core to translations on CoreTC.  But we should probably update considerTargets and inlineTargets.
completionQuery :: CommandLineState -> CompletionType -> IO (TranslateH CoreTC [String])
completionQuery _ ConsiderC = return $ promoteT considerTargets >>^ ((++ map fst considerables) . map ('\'':))
completionQuery _ InlineC   = return $ promoteT inlineTargetsT  >>^ map ('\'':)
completionQuery s CommandC  = return $ pure (M.keys (cl_dict s))
-- Need to modify opts in completionType function. No key can be a suffix of another key.
completionQuery _ (AmbiguousC ts) = do
    putStrLn "\nCannot tab complete: ambiguous completion type."
    putStrLn $ "Possibilities: " ++ intercalate ", " (map show ts)
    return (pure [])

shellComplete :: MVar CommandLineState -> String -> String -> IO [Completion]
shellComplete mvar rPrev so_far = do
    st <- readMVar mvar
    targetQuery <- completionQuery st (completionType rPrev)
    -- (liftM.liftM) (map simpleCompletion . nub . filter (so_far `isPrefixOf`))
    --     $ queryS (cl_kernel st) (cl_cursor (cl_session st)) targetQuery
    -- TODO: I expect you want to build a silent version of the kernal_env for this query
    cl <- catchM (queryS (cl_kernel st) targetQuery (cl_kernel_env st) (cl_cursor st)) (\_ -> return [])
    return $ (map simpleCompletion . nub . filter (so_far `isPrefixOf`)) cl

setRunningScript :: MonadIO m => Bool -> CLM m ()
setRunningScript b = modify $ \st -> st { cl_running_script = b }

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
    , "  - type \"consider 'foo\", where \"foo\" is a function"
    , "    defined in the module;"
    , "  - type \"set-pp-type Show\" to display full type information;"
    , "  - type \"info\" for more information about the current node;"
    , "  - to descend into a child node, type the name of the child"
    , "    (\"info\" includes a list of children of the current node);"
    , "  - to ascend, use the \"up\" command;"
    , "  - type \"log\" to display an activity log."
    , "=============================================================="
    ]

getTermDimensions :: IO (Int, Int)
getTermDimensions = do
    term <- setupTermFromEnv
    let w = fromMaybe 80 $ getCapability term termColumns
        h = fromMaybe 30 $ getCapability term termLines
    return (w,h)

-- | The first argument includes a list of files to load.
commandLine :: MonadIO m => [GHC.CommandLineOption] -> Behavior -> [External] -> CLM m ()
commandLine opts behavior exts = do
    let dict = mkDict $ shell_externals ++ exts
        ws_complete = " ()"
        (flags, filesToLoad) = partition (isPrefixOf "-") opts

    var <- liftIO $ atomically $ newTVar M.empty
    (w,h) <- liftIO getTermDimensions

    -- initialize shell-instance specific parts of the state
    -- TODO: move into another transformer layer?
    initState <- get
    let clState = initState { cl_tick        = var 
                            , cl_version     = VersionStore { vs_graph = [] , vs_tags = [] }
                            , cl_scripts     = []
                            , cl_dict        = dict
                            , cl_pretty_opts = (cl_pretty_opts initState) { po_width = w }
                            , cl_height      = h
                            }
    put clState

    completionMVar <- liftIO $ newMVar clState

    let loop = do
            st <- get
            let SAST n = cl_cursor st
            mLine <- liftIO $ if cl_nav st
                              then getNavCmd
                              else do modifyMVar_ completionMVar (const $ return st) -- so the completion can get the current state
                                      runInputTBehavior 
                                        behavior
                                        (setComplete (completeWordWithPrev Nothing ws_complete (shellComplete completionMVar)) defaultSettings)
                                        (getInputLine $ "hermit<" ++ show n ++ "> ")

            case mLine of
                Nothing          -> performMetaCommand Resume
                Just ('-':'-':_) -> loop
                Just line        -> if all isSpace line
                                    then loop
                                    else (evalScript line `ourCatch` cl_putStrLn) >> loop

    -- Display the banner
    if any (`elem` ["-v0", "-v1"]) flags
        then return ()
        else cl_putStrLn banner
    
    -- Load and run any scripts
    setRunningScript True
    sequence_ [ performMetaCommand $ case fileName of
                 "abort"  -> Abort
                 "resume" -> Resume
                 _        -> loadAndRun fileName
              | fileName <- reverse filesToLoad
              , not (null fileName)
              ] `ourCatch` \ msg -> cl_putStrLn $ "Booting Failure: " ++ msg
    setRunningScript False
    
    -- Start the CLI
    showWindow >> loop

ourCatch :: MonadIO m => CLM m () -> (String -> CLM m ()) -> CLM m ()
ourCatch m failure = catchM m $ \ msg -> ifM (gets cl_failhard) (performQuery Display >> cl_putStrLn msg >> abort) (failure msg)

evalScript :: MonadIO m => String -> CLM m ()
evalScript = parseScriptCLM >=> runScript

parseScriptCLM :: Monad m => String -> CLM m Script
parseScriptCLM = either fail return . parseScript

runScript :: MonadIO m => Script -> CLM m ()
runScript = mapM_ runExprH

runExprH :: MonadIO m => ExprH -> CLM m ()
runExprH expr = do
    dict <- gets cl_dict
    runKureM (\case
                 KernelEffect effect -> performKernelEffect effect expr
                 ShellEffect effect  -> performShellEffect effect
                 QueryFun query      -> performQuery query
                 MetaCommand meta    -> performMetaCommand meta
             )
             fail
             (interpExprH dict interpShellCommand expr)

-------------------------------------------------------------------------------

-- TODO: This can be refactored. We always showWindow. Also, Perhaps return a modifier, not ()
--   UPDATE: Not true.  We don't always showWindow.
-- TODO: All of these should through an exception if they fail to execute the command as given.

performKernelEffect :: MonadIO m => KernelEffect -> ExprH -> CLM m ()
performKernelEffect (Apply rr) expr = do
    st <- get

    let sk = cl_kernel st
        kEnv = cl_kernel_env st

    sast' <- prefixFailMsg "Rewrite failed: " $ applyS sk rr kEnv (cl_cursor st)

    let commit = put (newSAST expr sast' st) >> showWindow

    if cl_corelint st
        then do ast' <- toASTS sk sast'
                liftIO (queryK (kernelS sk) ast' lintModuleT kEnv)
                >>= runKureM (\ warns -> putStrToConsole warns >> commit)
                             (\ errs  -> liftIO (deleteS sk sast') >> fail errs)
        else commit

performKernelEffect (Pathfinder t) expr = do
    st <- get
    -- An extension to the Path
    p <- prefixFailMsg "Cannot find path: " $ queryS (cl_kernel st) t (cl_kernel_env st) (cl_cursor st)
    ast <- prefixFailMsg "Path is invalid: " $ modPathS (cl_kernel st) (<> p) (cl_kernel_env st) (cl_cursor st)
    put $ newSAST expr ast st
    showWindow

performKernelEffect (Direction dir) expr = do
    st <- get
    ast <- prefixFailMsg "Invalid move: " $ modPathS (cl_kernel st) (moveLocally dir) (cl_kernel_env st) (cl_cursor st)
    put $ newSAST expr ast st
    showWindow

performKernelEffect BeginScope expr = do
        st <- get
        ast <- beginScopeS (cl_kernel st) (cl_cursor st)
        put $ newSAST expr ast st
        showWindow

performKernelEffect EndScope expr = do
        st <- get
        ast <- endScopeS (cl_kernel st) (cl_cursor st)
        put $ newSAST expr ast st
        showWindow

performKernelEffect (Delete sast) _ = gets cl_kernel >>= flip deleteS sast

performKernelEffect (CorrectnessCritera q) expr = do
        st <- get
        -- TODO: Again, we may want a quiet version of the kernel_env
        modFailMsg (\ err -> unparseExprH expr ++ " [exception: " ++ err ++ "]")
                 $ queryS (cl_kernel st) q (cl_kernel_env st) (cl_cursor st)
        putStrToConsole $ unparseExprH expr ++ " [correct]"

-------------------------------------------------------------------------------

performShellEffect :: MonadIO m => ShellEffect -> CLM m ()
performShellEffect (CLSModify f) = do
    st <- get
    opt <- liftIO (fmap Right (f st) `catch` \ str -> return (Left str))
    case opt of
        Right st' -> put st' >> showWindow
        Left err  -> fail err

-------------------------------------------------------------------------------

performQuery :: MonadIO m => QueryFun -> CLM m ()
performQuery (QueryString q) = do
    st <- get
    str <- prefixFailMsg "Query failed: " $ queryS (cl_kernel st) q (cl_kernel_env st) (cl_cursor st)
    putStrToConsole str

performQuery (QueryDocH q) = do
    st <- get
    doc <- prefixFailMsg "Query failed: " $ queryS (cl_kernel st) (q (initPrettyC $ cl_pretty_opts st) $ cl_pretty st) (cl_kernel_env st) (cl_cursor st)
    liftIO $ cl_render st stdout (cl_pretty_opts st) (Right doc)

performQuery (Inquiry f) = do
    st <- get
    str <- liftIO $ f st
    putStrToConsole str

-- These two need to use Inquiry
-- performQuery (Message msg) = liftIO (putStrLn msg)
-- Explicit calls to display should work no matter what the loading state is.
performQuery Display = do
    running_script_st <- gets cl_running_script
    setRunningScript False
    showWindow
    setRunningScript running_script_st

-------------------------------------------------------------------------------

performMetaCommand :: MonadIO m => MetaCommand -> CLM m ()
performMetaCommand (SeqMeta ms) = mapM_ performMetaCommand ms
performMetaCommand Abort  = abort
performMetaCommand Resume = do
    st <- get
    sast' <- applyS (cl_kernel st) occurAnalyseAndDezombifyR (cl_kernel_env st) (cl_cursor st)
    resume sast'

performMetaCommand Continue = get >>= continue
performMetaCommand (Dump fileName _pp renderer width) = do
    st <- get
    case lookup renderer shellRenderers of
      Just r -> do doc <- prefixFailMsg "Bad renderer option: " $
                            queryS (cl_kernel st) (liftPrettyH (cl_pretty_opts st) $ cl_pretty st) (cl_kernel_env st) (cl_cursor st)
                   liftIO $ do h <- openFile fileName WriteMode
                               r h ((cl_pretty_opts st) { po_width = width }) (Right doc)
                               hClose h
      _ -> fail "dump: bad pretty-printer or renderer option"

performMetaCommand (LoadFile scriptName fileName) =
  do putStrToConsole $ "Loading \"" ++ fileName ++ "\"..."
     res <- liftIO $ try (readFile fileName)
     case res of
       Left (err :: IOException) -> fail ("IO error: " ++ show err)
       Right str -> do script <- parseScriptCLM str
                       modify $ \ st -> st {cl_scripts = (scriptName,script) : cl_scripts st}
                       putStrToConsole ("Script \"" ++ scriptName ++ "\" loaded successfully from \"" ++ fileName ++ "\".")

performMetaCommand (SaveFile fileName) =
  do version <- gets cl_version
     putStrToConsole $ "[saving " ++ fileName ++ "]"
     -- no checks to see if you are clobering; be careful
     liftIO $ writeFile fileName $ showGraph (vs_graph version) (vs_tags version) (SAST 0)

performMetaCommand (ScriptToRewrite rewriteName scriptName) =
  do script <- lookupScript scriptName
     st <- get
     dict' <- iokm2clm "script-to-rewrite failed: " (return $ addScriptToDict rewriteName script (cl_dict st))
     put (st {cl_dict = dict'})
     putStrToConsole ("Rewrite \"" ++ rewriteName ++ "\" defined successfully.")

performMetaCommand (DefineScript scriptName str) =
  do script <- parseScriptCLM str
     modify $ \ st -> st {cl_scripts = (scriptName,script) : cl_scripts st}
     putStrToConsole ("Script \"" ++ scriptName ++ "\" defined successfully.")

performMetaCommand (RunScript scriptName) =
  do script <- lookupScript scriptName
     running_script_st <- gets cl_running_script
     setRunningScript True
     runScript script `catchError` (\ err -> setRunningScript running_script_st >> throwError err)
     setRunningScript running_script_st
     putStrToConsole ("Script \"" ++ scriptName ++ "\" ran successfully.")
     showWindow

performMetaCommand (SaveScript fileName scriptName) =
  do script <- lookupScript scriptName
     putStrToConsole $ "Saving script \"" ++ scriptName ++ "\" to file \"" ++ fileName ++ "\"."
     liftIO $ writeFile fileName $ unparseScript script
     putStrToConsole $ "Save successful."

lookupScript :: Monad m => ScriptName -> CLM m Script
lookupScript scriptName = do scripts <- gets cl_scripts
                             case lookup scriptName scripts of
                               Nothing     -> fail $ "No script of name " ++ scriptName ++ " is loaded."
                               Just script -> return script

-------------------------------------------------------------------------------

-- TODO: merge with cl_putStr defn
putStrToConsole :: MonadIO m => String -> CLM m ()
putStrToConsole str = ifM (gets cl_running_script)
                          (return ())
                          (cl_putStrLn str)

--------------------------------------------------------

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

----------------------------------------------------------------------------------------------

cl_kernel_env  :: CommandLineState -> HermitMEnv
cl_kernel_env st =
    let out str = do (r,_) <- GHC.liftIO $ runCLM st $ cl_putStrLn str
                     either (\case CLError msg -> fail msg
                                   _           -> fail "resume abort called from cl_putStrLn (impossible!)")
                            return r
                        
    in  mkHermitMEnv $ \ msg -> case msg of
                DebugTick    msg'      -> do
                        c <- GHC.liftIO $ tick (cl_tick st) msg'
                        out $ "<" ++ show c ++ "> " ++ msg'
                DebugCore  msg' cxt core -> do
                        out $ "[" ++ msg' ++ "]"
                        doc :: DocH <- apply (cl_pretty st) (liftPrettyC (cl_pretty_opts st) cxt) (inject core)
                        GHC.liftIO $ cl_render st stdout (cl_pretty_opts st) (Right doc)

-- tick counter
tick :: TVar (M.Map String Int) -> String -> IO Int
tick var msg = atomically $ do
        m <- readTVar var
        let c = case M.lookup msg m of
                Nothing -> 1
                Just x  -> x + 1
        writeTVar var (M.insert msg c m)
        return c

----------------------------------------------------------------------------------------------

