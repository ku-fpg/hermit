{-# LANGUAGE LambdaCase, ScopedTypeVariables, GADTs, FlexibleContexts #-}

module HERMIT.Shell.Command
    ( -- * The HERMIT Command-line Shell
      commandLine
    , unicodeConsole
    , diffDocH
    , diffR
      -- ** Exported for hermit-web
    , performKernelEffect
    , performQuery
    , performShellEffect
    , cl_kernel_env
    , getFocusPath
    , shellComplete
    , evalScript
    ) where

import Control.Applicative
import Control.Arrow hiding (loop)
import Control.Concurrent
import Control.Exception.Base hiding (catch)
import Control.Monad.State
import Control.Monad.Error

import Data.Char
import Data.Monoid
import Data.List (intercalate, isInfixOf, isPrefixOf, isSuffixOf, nub, partition)
import qualified Data.Map as M
import Data.Maybe

import HERMIT.Core
import HERMIT.Dictionary
import HERMIT.External
import qualified HERMIT.GHC as GHC
import HERMIT.Kernel (queryK, AST)
import HERMIT.Kernel.Scoped hiding (abortS, resumeS)
import HERMIT.Kure
import HERMIT.Parser

import HERMIT.Plugin.Display
import HERMIT.Plugin.Types

import HERMIT.PrettyPrinter.Common
import HERMIT.PrettyPrinter.Clean (ppCoreTC)

import HERMIT.Shell.Dictionary
import HERMIT.Shell.Externals
import HERMIT.Shell.Interpreter
import HERMIT.Shell.Proof
import HERMIT.Shell.Renderer
import HERMIT.Shell.ScriptToRewrite
import HERMIT.Shell.Types

import System.IO
import System.IO.Temp
import System.Process

-- import System.Console.ANSI
import System.Console.Haskeline hiding (catch, display)

----------------------------------------------------------------------------------

catch :: IO a -> (String -> IO a) -> IO a
catch = catchJust (\ (err :: IOException) -> return (show err))

fixWindow :: MonadIO m => CLT m ()
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

showWindow :: MonadIO m => CLT m ()
showWindow = fixWindow >> gets cl_window >>= pluginM . display . Just

-------------------------------------------------------------------------------

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

completionQuery :: CommandLineState -> CompletionType -> IO (TranslateH CoreTC [String])
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

shellComplete :: MVar CommandLineState -> String -> String -> IO [Completion]
shellComplete mvar rPrev so_far = do
    st <- readMVar mvar
    targetQuery <- completionQuery st (completionType rPrev)
    -- (liftM.liftM) (map simpleCompletion . nub . filter (so_far `isPrefixOf`))
    --     $ queryS (cl_kernel st) (cl_cursor (cl_session st)) targetQuery
    -- TODO: I expect you want to build a silent version of the kernal_env for this query
    cl <- catchM (queryS (cl_kernel st) targetQuery (cl_kernel_env st) (cl_cursor st)) (\_ -> return [])
    return $ (map simpleCompletion . nub . filter (so_far `isPrefixOf`)) cl

setRunningScript :: MonadIO m => Bool -> CLT m ()
setRunningScript b = modify $ \st -> st { cl_pstate = (cl_pstate st) { ps_running_script = b } }

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
                                    else (evalScript line `ourCatch` cl_putStrLn) >> loop

    -- Display the banner
    if any (`elem` ["-v0", "-v1"]) flags
        then return ()
        else cl_putStrLn banner

    -- Load and run any scripts
    setRunningScript True
    sequence_ [ performShellEffect $ case fileName of
                 "abort"  -> Abort
                 "resume" -> Resume
                 _        -> loadAndRun fileName
              | fileName <- reverse filesToLoad
              , not (null fileName)
              ] `ourCatch` \ msg -> cl_putStrLn $ "Booting Failure: " ++ msg
    setRunningScript False

    -- Start the CLI
    showWindow
    let settings = setComplete (completeWordWithPrev Nothing ws_complete (shellComplete completionMVar)) defaultSettings
    (r,s) <- get >>= liftIO . runInputTBehavior behavior settings . flip runCLT loop
    either throwError (\v -> put s >> return v) r

ourCatch :: MonadIO m => CLT m () -> (String -> CLT m ()) -> CLT m ()
ourCatch m failure = catchM m $ \ msg -> ifM (gets cl_failhard) (performQuery Display >> cl_putStrLn msg >> abort) (failure msg)

evalScript :: MonadIO m => String -> CLT m ()
evalScript = parseScriptCLT >=> runScript

parseScriptCLT :: Monad m => String -> CLT m Script
parseScriptCLT = either fail return . parseScript

runScript :: MonadIO m => Script -> CLT m ()
runScript = mapM_ runExprH

runExprH :: MonadIO m => ExprH -> CLT m ()
runExprH expr = prefixFailMsg ("Error in expression: " ++ unparseExprH expr ++ "\n") $ do
    shellCmd <- interpExprH interpShellCommand expr
    case shellCmd of
        KernelEffect effect -> performKernelEffect effect expr
        ShellEffect effect  -> performShellEffect effect
        QueryFun query      -> performQuery query
        ProofCommand cmd    -> performProofCommand cmd

ppWholeProgram :: MonadIO m => AST -> CLT m DocH
ppWholeProgram ast = do
    st <- get
    liftIO (queryK (kernelS $ cl_kernel st)
            ast
            (extractT $ pathT [ModGuts_Prog] $ liftPrettyH (cl_pretty_opts st) $ cl_pretty st)
            (cl_kernel_env st)) >>= runKureM return fail

-------------------------------------------------------------------------------

-- TODO: This can be refactored. We always showWindow. Also, Perhaps return a modifier, not ()
--   UPDATE: Not true.  We don't always showWindow.
-- TODO: All of these should through an exception if they fail to execute the command as given.

performKernelEffect :: MonadIO m => KernelEffect -> ExprH -> CLT m ()
performKernelEffect (Apply rr) expr = do
    st <- get

    let sk = cl_kernel st
        kEnv = cl_kernel_env st
        sast = cl_cursor st
        ppOpts = cl_pretty_opts st

    sast' <- prefixFailMsg "Rewrite failed: " $ applyS sk rr kEnv sast

    let commit = put (newSAST expr sast' st) >> showResult
        showResult = if cl_diffonly st then showDiff else showWindow
        showDiff = do doc1 <- queryS sk (liftPrettyH ppOpts (cl_pretty st)) kEnv sast
                      doc2 <- queryS sk (liftPrettyH ppOpts (cl_pretty st)) kEnv sast'
                      diffDocH ppOpts doc1 doc2 >>= cl_putStr

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

performQuery :: MonadIO m => QueryFun -> CLT m ()
performQuery (QueryString q) = do
    st <- get
    str <- prefixFailMsg "Query failed: " $ queryS (cl_kernel st) q (cl_kernel_env st) (cl_cursor st)
    putStrToConsole str

performQuery (QueryDocH q) = do
    st <- get
    doc <- prefixFailMsg "Query failed: " $ queryS (cl_kernel st) (q (initPrettyC $ cl_pretty_opts st) $ cl_pretty st) (cl_kernel_env st) (cl_cursor st)
    liftIO $ cl_render st stdout (cl_pretty_opts st) (Right doc)

performQuery (Inquiry f) = get >>= liftIO . f >>= putStrToConsole

performQuery (Diff s1 s2) = do
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

    r <- diffDocH (cl_pretty_opts st) doc1 doc2

    cl_putStrLn "Diff:"
    cl_putStrLn "====="
    cl_putStr r

-- Explicit calls to display should work no matter what the loading state is.
performQuery Display = do
    running_script_st <- gets cl_running_script
    setRunningScript False
    showWindow
    setRunningScript running_script_st

-------------------------------------------------------------------------------

performShellEffect :: MonadIO m => ShellEffect -> CLT m ()
performShellEffect (SeqMeta ms) = mapM_ performShellEffect ms
performShellEffect Abort  = abort
performShellEffect Resume = do
    st <- get
    sast' <- applyS (cl_kernel st) occurAnalyseAndDezombifyR (cl_kernel_env st) (cl_cursor st)
    resume sast'

performShellEffect Continue = get >>= continue
performShellEffect (Dump fileName renderer width) = do
    st <- get
    case lookup renderer shellRenderers of
      Just r -> do doc <- prefixFailMsg "Bad renderer option: " $
                            queryS (cl_kernel st) (liftPrettyH (cl_pretty_opts st) $ cl_pretty st) (cl_kernel_env st) (cl_cursor st)
                   liftIO $ do h <- openFile fileName WriteMode
                               r h ((cl_pretty_opts st) { po_width = width }) (Right doc)
                               hClose h
      _ -> fail "dump: bad pretty-printer or renderer option"

performShellEffect (LoadFile scriptName fileName) =
  do putStrToConsole $ "Loading \"" ++ fileName ++ "\"..."
     res <- liftIO $ try (readFile fileName)
     case res of
       Left (err :: IOException) -> fail ("IO error: " ++ show err)
       Right str -> do script <- parseScriptCLT str
                       modify $ \ st -> st {cl_scripts = (scriptName,script) : cl_scripts st}
                       putStrToConsole ("Script \"" ++ scriptName ++ "\" loaded successfully from \"" ++ fileName ++ "\".")

performShellEffect (SaveFile fileName) =
  do version <- gets cl_version
     putStrToConsole $ "[saving " ++ fileName ++ "]"
     -- no checks to see if you are clobering; be careful
     liftIO $ writeFile fileName $ showGraph (vs_graph version) (vs_tags version) (SAST 0)

performShellEffect (ScriptToRewrite rewriteName scriptName) =
  do script <- lookupScript scriptName
     addScriptToDict rewriteName script 
     putStrToConsole ("Rewrite \"" ++ rewriteName ++ "\" defined successfully.")

performShellEffect (DefineScript scriptName str) =
  do script <- parseScriptCLT str
     modify $ \ st -> st {cl_scripts = (scriptName,script) : cl_scripts st}
     putStrToConsole ("Script \"" ++ scriptName ++ "\" defined successfully.")

performShellEffect (RunScript scriptName) =
  do script <- lookupScript scriptName
     running_script_st <- gets cl_running_script
     setRunningScript True
     runScript script `catchError` (\ err -> setRunningScript running_script_st >> throwError err)
     setRunningScript running_script_st
     putStrToConsole ("Script \"" ++ scriptName ++ "\" ran successfully.")
     showWindow

performShellEffect (SaveScript fileName scriptName) =
  do script <- lookupScript scriptName
     putStrToConsole $ "Saving script \"" ++ scriptName ++ "\" to file \"" ++ fileName ++ "\"."
     liftIO $ writeFile fileName $ unparseScript script
     putStrToConsole $ "Save successful."

performShellEffect (CLSModify f) = do
    st <- get
    opt <- liftIO (fmap Right (f st) `catch` \ str -> return (Left str))
    case opt of
        Right st' -> put st' >> showWindow
        Left err  -> fail err

-------------------------------------------------------------------------------

-- TODO: merge with cl_putStr defn
putStrToConsole :: MonadIO m => String -> CLT m ()
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

-- TODO: this should be in PrettyPrinter.Common, but is here because it relies on
--       unicodeConsole to get nice colored diffs. We can either switch to straight unicode
--       renderer and give up on color, or come up with a clever solution.
diffDocH :: (MonadCatch m, MonadIO m) => PrettyOptions -> DocH -> DocH -> m String
diffDocH opts doc1 doc2 =
    liftAndCatchIO $
        withSystemTempFile "A.dump" $ \ fp1 h1 ->
            withSystemTempFile "B.dump" $ \ fp2 h2 ->
                withSystemTempFile "AB.diff" $ \ fp3 h3 -> do
                    unicodeConsole h1 opts (Right doc1)
                    hFlush h1
                    unicodeConsole h2 opts (Right doc2)
                    hFlush h2
                    let cmd = unwords ["diff", "-b", "-U 5", fp1, fp2]
                        p = (shell cmd) { std_out = UseHandle h3 , std_err = UseHandle h3 }
                    (_,_,_,h) <- createProcess p
                    _ <- waitForProcess h
                    res <- readFile fp3
                    -- strip out some of the diff lines
                    return $ unlines [ l | l <- lines res, not (fp1 `isInfixOf` l || fp2 `isInfixOf` l)
                                                         , not ("@@" `isPrefixOf` l && "@@" `isSuffixOf` l) ]

-- TODO: again this should be elsewhere, but is here because diffDocH is here.
diffR :: Injection a CoreTC => PrettyOptions -> String -> RewriteH a -> RewriteH a
diffR opts msg rr = do
    let pp = extractT $ liftPrettyH opts ppCoreTC
        runDiff b a = do
            doc1 <- return b >>> pp
            doc2 <- return a >>> pp
            r <- diffDocH opts doc1 doc2
            return a >>> traceR (msg ++ " diff:\n" ++ r)

    -- Be careful to only run the rr once, in case it has side effects.
    (e,r) <- idR &&& attemptM rr
    either fail (runDiff e) r

