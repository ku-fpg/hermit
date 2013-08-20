{-# LANGUAGE LambdaCase, ScopedTypeVariables, GADTs #-}

module HERMIT.Shell.Command
       ( -- * The HERMIT Command-line Shell
         commandLine
       , unicodeConsole
) where

import qualified GhcPlugins as GHC

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
import Data.Default (def)
import qualified Data.Map as M
import Data.Maybe

import HERMIT.Monad
import HERMIT.Kure
import HERMIT.Dictionary
import HERMIT.External
import HERMIT.Interp
import HERMIT.Kernel (queryK)
import HERMIT.Kernel.Scoped
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

import qualified Text.PrettyPrint.MarkedHughesPJ as PP

-- import System.Console.ANSI
import System.Console.Haskeline hiding (catch)
import System.Console.Terminfo (setupTermFromEnv, getCapability, termColumns, termLines)

----------------------------------------------------------------------------------

catch :: IO a -> (String -> IO a) -> IO a
catch = catchJust (\ (err :: IOException) -> return (show err))

pretty :: CommandLineState -> PrettyH CoreTC
pretty st = case M.lookup (cl_pretty st) pp_dictionary of
                Just pp -> pp
                Nothing -> pure (PP.text $ "<<no pretty printer for " ++ cl_pretty st ++ ">>")

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
getFocusPath = get >>= \ st -> liftM concat $ iokm2clm "getFocusPath - pathS failed: " $ pathS (cl_kernel st) (cl_cursor st)

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
                   (liftIO . cl_render st stdout ppOpts)
                   (toASTS skernel (cl_cursor st) >>= liftKureM >>= \ ast ->
                        queryK (kernelS skernel) ast (extractT $ pathT (cl_window st) $ liftPrettyH ppOpts $ pretty st) (cl_kernel_env st))
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
    mcls <- queryS (cl_kernel st) (cl_cursor st) targetQuery (cl_kernel_env st)
    cl <- runKureM return (\ _ -> return []) mcls
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
    , "    (\"info\" includes a list of children of the current node\");"
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
commandLine :: [GHC.CommandLineOption] -> Behavior -> [External] -> ScopedKernel -> SAST -> IO ()
commandLine opts behavior exts skernel sast = do
    let dict = mkDict $ shell_externals ++ exts
    let ws_complete = " ()"
    let (flags, filesToLoad) = partition (isPrefixOf "-") opts

    let startup = do
            if any (`elem` ["-v0", "-v1"]) flags
                then return ()
                else liftIO $ putStrLn banner
            setRunningScript True
            sequence_ [ performMetaCommand $ case fileName of
                         "abort"  -> Abort
                         "resume" -> Resume
                         _        -> loadAndRun fileName
                      | fileName <- reverse filesToLoad
                      , not (null fileName)
                      ] `ourCatch` \ msg -> liftIO . putStrLn $ "Booting Failure: " ++ msg
            setRunningScript False

    var <- GHC.liftIO $ atomically $ newTVar M.empty
    (w,h) <- getTermDimensions

    let shellState = CommandLineState
                       { cl_cursor         = sast
                       , cl_pretty         = "clean"
                       , cl_pretty_opts    = def { po_width = w }
                       , cl_render         = unicodeConsole
                       , cl_height         = h
                       , cl_nav            = False
                       , cl_running_script = False
                       , cl_tick          = var
                       , cl_corelint      = False
                       , cl_failhard      = False
                       , cl_window        = mempty
                       , cl_dict          = dict
                       , cl_scripts       = []
                       , cl_kernel        = skernel
                       , cl_initSAST      = sast
                       , cl_version       = VersionStore
                                              { vs_graph = []
                                              , vs_tags  = []
                                              }
                       }

    completionMVar <- newMVar shellState

    _ <- runInputTBehavior behavior
                (setComplete (completeWordWithPrev Nothing ws_complete (shellComplete completionMVar)) defaultSettings)
                (evalStateT (runErrorT (startup >> showWindow >> loop completionMVar)) shellState)

    return ()

loop :: (MonadIO m, m ~ InputT IO) => MVar CommandLineState -> CLM m ()
loop completionMVar = loop'
  where loop' = do
            st <- get
            -- so the completion can get the current state
            liftIO $ modifyMVar_ completionMVar (const $ return st)
            -- liftIO $ print (cl_pretty st, cl_cursor (cl_session st))
            let SAST n = cl_cursor st
            maybeLine <- if cl_nav st
                           then liftIO getNavCmd
                           else do {- TODO: for an inplace CLI...
                                   liftIO $ do setCursorPosition (cl_height st - 3) 0
                                               setSGR [ SetSwapForegroundBackground True ]
                                               putStrLn $ replicate (po_width (cl_pretty_opts st)) ' '
                                               setSGR [ SetSwapForegroundBackground False ] -}
                                   lift $ lift $ getInputLine $ "hermit<" ++ show n ++ "> "

            case maybeLine of
                Nothing             -> performMetaCommand Resume
                Just ('-':'-':_msg) -> loop'
                Just line           ->
                    if all isSpace line
                    then loop'
                    else (case parseStmtsH line of
                                Left  msg   -> throwError ("Parse failure: " ++ msg)
                                Right stmts -> evalStmts stmts)
                         `ourCatch` (liftIO . putStrLn)
                           >> loop'

ourCatch :: MonadIO m => CLM IO () -> (String -> CLM m ()) -> CLM m ()
ourCatch m failure = do
    st <- get
    (res,st') <- liftIO $ runStateT (runErrorT m) st
    put st'
    case res of
        Left msg -> if cl_failhard st'
                    then do
                        performQuery Display
                        liftIO $ putStrLn msg >> abortS (cl_kernel st')
                    else failure msg
        Right () -> return ()

evalStmts :: MonadIO m => [ExprH] -> CLM m ()
evalStmts = mapM_ evalExpr

evalExpr :: MonadIO m => ExprH -> CLM m ()
evalExpr expr = do
    dict <- gets cl_dict
    runKureM (\case
                 AstEffect effect   -> performAstEffect effect expr
                 ShellEffect effect -> performShellEffect effect
                 QueryFun query     -> performQuery query
                 MetaCommand meta   -> performMetaCommand meta
             )
             throwError
             (interpExprH dict interpShellCommand expr)

-------------------------------------------------------------------------------

-- TODO: This can be refactored. We always showWindow. Also, Perhaps return a modifier, not ()
--   UPDATE: Not true.  We don't always showWindow.
-- TODO: All of these should through an exception if they fail to execute the command as given.

performAstEffect :: MonadIO m => AstEffect -> ExprH -> CLM m ()
performAstEffect (Apply rr) expr = do
    st <- get

    let sk = cl_kernel st
        kEnv = cl_kernel_env st

    sast' <- iokm2clm "Rewrite failed: " $ applyS sk (cl_cursor st) rr kEnv

    let commit = put (newSAST expr sast' st) >> showWindow

    if cl_corelint st
        then do ast' <- iokm2clm'' $ toASTS sk sast'
                liftIO (queryK (kernelS sk) ast' lintModuleT kEnv)
                >>= runKureM (\ warns -> putStrToConsole warns >> commit)
                             (\ errs  -> liftIO (deleteS sk sast') >> fail errs)
        else commit

performAstEffect (Pathfinder t) expr = do
    st <- get
    -- An extension to the Path
    iokm2clm' "Cannot find path: "
              (\ p -> do ast <- iokm2clm "Path is invalid: " $ modPathS (cl_kernel st) (cl_cursor st) (<> p) (cl_kernel_env st)
                         put $ newSAST expr ast st
                         showWindow)
              (queryS (cl_kernel st) (cl_cursor st) t (cl_kernel_env st))

performAstEffect (Direction dir) expr = do
    st <- get
    ast <- iokm2clm "Invalid move: " $ modPathS (cl_kernel st) (cl_cursor st) (moveLocally dir) (cl_kernel_env st)
    put $ newSAST expr ast st
    showWindow

performAstEffect BeginScope expr = do
        st <- get
        ast <- iokm2clm'' $ beginScopeS (cl_kernel st) (cl_cursor st)
        put $ newSAST expr ast st
        showWindow

performAstEffect EndScope expr = do
        st <- get
        ast <- iokm2clm'' $ endScopeS (cl_kernel st) (cl_cursor st)
        put $ newSAST expr ast st
        showWindow

performAstEffect (Tag tag) _ = do
        st <- get
        put $ st { cl_version = (cl_version st) { vs_tags = (tag, cl_cursor st) : vs_tags (cl_version st) }}

performAstEffect (CorrectnessCritera q) expr = do
        st <- get
        -- TODO: Again, we may want a quiet version of the kernel_env
        liftIO (queryS (cl_kernel st) (cl_cursor st) q (cl_kernel_env st))
          >>= runKureM (\ () -> putStrToConsole $ unparseExprH expr ++ " [correct]")
                       (\ err -> fail $ unparseExprH expr ++ " [exception: " ++ err ++ "]")

-------------------------------------------------------------------------------

performShellEffect :: MonadIO m => ShellEffect -> CLM m ()
performShellEffect (CLSModify f) = do
    st <- get
    opt <- liftIO (fmap Right (f st) `catch` \ str -> return (Left str))
    case opt of
        Right st' -> put st' >> showWindow
        Left err  -> throwError err

-------------------------------------------------------------------------------

performQuery :: MonadIO m => QueryFun -> CLM m ()
performQuery (QueryString q) = do
    st <- get
    iokm2clm' "Query failed: "
              putStrToConsole
              (queryS (cl_kernel st) (cl_cursor st) q (cl_kernel_env st))

performQuery (QueryDocH q) = do
    st <- get
    iokm2clm' "Query failed: "
              (liftIO . cl_render st stdout (cl_pretty_opts st))
              (queryS (cl_kernel st) (cl_cursor st) (q (initPrettyC $ cl_pretty_opts st) $ pretty st) (cl_kernel_env st))

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
performMetaCommand Abort  = gets cl_kernel >>= (liftIO . abortS)
performMetaCommand Resume = do
    st <- get
    sast' <- iokm2clm "Final occurrence analysis failed (should never happen!): "
                    $ applyS (cl_kernel st) (cl_cursor st) occurrenceAnalysisR (cl_kernel_env st)
    iokm2clm'' $ resumeS (cl_kernel st) sast'

performMetaCommand (Delete sast) = gets cl_kernel >>= iokm2clm'' . flip deleteS sast
performMetaCommand (Dump fileName _pp renderer width) = do
    st <- get
    case (M.lookup (cl_pretty st) pp_dictionary,lookup renderer finalRenders) of
      (Just pp, Just r) -> do doc <- iokm2clm "Bad pretty-printer or renderer option: " $
                                         queryS (cl_kernel st) (cl_cursor st) (liftPrettyH (cl_pretty_opts st) pp) (cl_kernel_env st)
                              liftIO $ do h <- openFile fileName WriteMode
                                          r h ((cl_pretty_opts st) { po_width = width }) doc
                                          hClose h
      _ -> throwError "dump: bad pretty-printer or renderer option"

performMetaCommand (LoadFile scriptName fileName) =
  do putStrToConsole $ "Loading \"" ++ fileName ++ "\"..."
     res <- liftIO $ try (readFile fileName)
     case res of
       Left (err :: IOException) -> throwError ("IO error: " ++ show err)
       Right str -> case parseStmtsH str of
                      Left  msg    -> throwError ("Parse failure: " ++ msg)
                      Right script -> do modify $ \ st -> st {cl_scripts = (scriptName,script) : cl_scripts st}
                                         putStrToConsole ("Script \"" ++ scriptName ++ "\" loaded successfully from \"" ++ fileName ++ "\".")

performMetaCommand (SaveFile fileName) = do
        version <- gets cl_version
        putStrToConsole $ "[saving " ++ fileName ++ "]"
        -- no checks to see if you are clobering; be careful
        liftIO $ writeFile fileName $ showGraph (vs_graph version) (vs_tags version) (SAST 0)

performMetaCommand (ScriptToRewrite scriptName) =
  do st <- get
     case lookup scriptName (cl_scripts st) of
       Nothing     -> throwError ("No script of name " ++ scriptName ++ " is loaded.")
       Just script -> do dict' <- iokm2clm "define-rewrite failed: " (return $ addScriptToDict scriptName script (cl_dict st))
                         put (st {cl_dict = dict'})
                         putStrToConsole ("Rewrite \"" ++ scriptName ++ "\" defined successfully.")

performMetaCommand (DefineScript scriptName str) =
  case parseStmtsH str of
    Left  msg    -> throwError ("Parse failure: " ++ msg)
    Right script -> do modify $ \ st -> st {cl_scripts = (scriptName,script) : cl_scripts st}
                       putStrToConsole ("Script \"" ++ scriptName ++ "\" defined successfully.")

performMetaCommand (RunScript scriptName) =
  do st <- get
     case lookup scriptName (cl_scripts st) of
       Nothing     -> throwError ("No script of name " ++ scriptName ++ " is loaded.")
       Just script -> do running_script_st <- gets cl_running_script
                         setRunningScript True
                         evalStmts script `catchError` (\ err -> setRunningScript running_script_st >> throwError err)
                         setRunningScript running_script_st
                         putStrToConsole ("Script \"" ++ scriptName ++ "\" ran successfully.")
                         showWindow

performMetaCommand (SaveScript fileName scriptName) =
  do st <- get
     case lookup scriptName (cl_scripts st) of
       Nothing     -> throwError ("No script of name " ++ scriptName ++ " is loaded.")
       Just script -> do putStrToConsole $ "Saving script \"" ++ scriptName ++ "\" to file \"" ++ fileName ++ "\"."
                         liftIO $ writeFile fileName $ intercalate " ; " $ map unparseExprH script
                         putStrToConsole $ "Save successful."

-------------------------------------------------------------------------------

putStrToConsole :: MonadIO m => String -> CLM m ()
putStrToConsole str = ifM (gets cl_running_script)
                          (return ())
                          (liftIO $ putStrLn str)

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
cl_kernel_env st = mkHermitMEnv $ \ msg -> case msg of
                DebugTick    msg'      -> do
                        c <- GHC.liftIO $ tick (cl_tick st) msg'
                        GHC.liftIO $ putStrLn $ "<" ++ show c ++ "> " ++ msg'
                DebugCore  msg' cxt core -> do
                        GHC.liftIO $ putStrLn $ "[" ++ msg' ++ "]"
                        doc :: DocH <- apply (pretty st) (liftPrettyC (cl_pretty_opts st) cxt) (inject core)
                        GHC.liftIO $ cl_render st stdout (cl_pretty_opts st) doc

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

