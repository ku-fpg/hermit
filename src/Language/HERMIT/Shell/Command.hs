{-# LANGUAGE FlexibleInstances, FlexibleContexts, ScopedTypeVariables, GADTs, TypeFamilies, DeriveDataTypeable, LambdaCase #-}

module Language.HERMIT.Shell.Command
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
import Data.List (intercalate, isPrefixOf, nub)
import Data.Default (def)
import qualified Data.Map as M
import Data.Maybe

import Language.HERMIT.Monad
import Language.HERMIT.Kure
import Language.HERMIT.Dictionary
import Language.HERMIT.External
import Language.HERMIT.Interp
import Language.HERMIT.Kernel (queryK)
import Language.HERMIT.Kernel.Scoped
import Language.HERMIT.Parser
import Language.HERMIT.PrettyPrinter.Common

import Language.HERMIT.Primitive.GHC
import Language.HERMIT.Primitive.Inline
import Language.HERMIT.Primitive.Navigation

import Language.HERMIT.Shell.Externals
import Language.HERMIT.Shell.ImportR

import System.IO

import qualified Text.PrettyPrint.MarkedHughesPJ as PP

import System.Console.Haskeline hiding (catch)

----------------------------------------------------------------------------------

catch :: IO a -> (String -> IO a) -> IO a
catch = catchJust (\ (err :: IOException) -> return (show err))

pretty :: SessionState -> PrettyH CoreTC
pretty ss = case M.lookup (cl_pretty ss) pp_dictionary of
                Just pp -> pp
                Nothing -> pure (PP.text $ "<<no pretty printer for " ++ cl_pretty ss ++ ">>")

showFocus :: MonadIO m => CLM m ()
showFocus = do
    st <- get
    let ss = cl_session st
    -- No not show focus while loading
    ifM (gets (cl_loading . cl_session))
        (return ())
        (iokm2clm' "Rendering error: "
                   (liftIO . cl_render ss stdout (cl_pretty_opts ss))
                   (queryS (cl_kernel st) (cl_cursor ss) (liftPrettyH (cl_pretty_opts ss) $ pretty ss) (cl_kernel_env ss))
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
completionQuery _ InlineC   = return $ promoteT inlineTargets   >>^ map ('\'':)
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
    mcls <- queryS (cl_kernel st) (cl_cursor $ cl_session st) targetQuery (cl_kernel_env $ cl_session st)
    cl <- runKureM return (\ _ -> return []) mcls
    return $ (map simpleCompletion . nub . filter (so_far `isPrefixOf`)) cl

setLoading :: MonadIO m => Bool -> CLM m ()
setLoading b = modify $ \st -> st { cl_session = (cl_session st) { cl_loading = b } }

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

-- | The first argument is a list of files to load.
commandLine :: [FilePath] -> Behavior -> [External] -> ScopedKernel -> SAST -> IO ()
commandLine filesToLoad behavior exts skernel sast = do
    let dict = mkDict $ shell_externals ++ exts
    let ws_complete = " ()"

    let startup = do
            liftIO $ putStrLn banner
            setLoading True
            sequence_ [ performMetaCommand $ case fileName of
                         "abort"  -> Abort
                         "resume" -> Resume
                         _        -> LoadFile fileName
                      | fileName <- reverse filesToLoad
                      , not (null fileName)
                      ] `ourCatch` \ msg -> liftIO . putStrLn $ "Booting Failure: " ++ msg
            setLoading False

    var <- GHC.liftIO $ atomically $ newTVar M.empty

    let sessionState = SessionState sast "clean" def unicodeConsole 80 False False var False False
        shellState = CommandLineState [] [] dict skernel sast sessionState

    completionMVar <- newMVar shellState

    _ <- runInputTBehavior behavior
                (setComplete (completeWordWithPrev Nothing ws_complete (shellComplete completionMVar)) defaultSettings)
                (evalStateT (runErrorT (startup >> showFocus >> loop completionMVar)) shellState)

    return ()

loop :: (MonadIO m, m ~ InputT IO) => MVar CommandLineState -> CLM m ()
loop completionMVar = loop'
  where loop' = do
            st <- get
            -- so the completion can get the current state
            liftIO $ modifyMVar_ completionMVar (const $ return st)
            -- liftIO $ print (cl_pretty st, cl_cursor (cl_session st))
            let SAST n = cl_cursor (cl_session st)
            maybeLine <- if cl_nav (cl_session st)
                           then liftIO getNavCmd
                           else lift $ lift $ getInputLine $ "hermit<" ++ show n ++ "> "

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
        Left msg -> if cl_failhard (cl_session st')
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

-- TODO: This can be refactored. We always showFocus. Also, Perhaps return a modifier, not ()
--   UPDATE: Not true.  We don't always showFocus.
-- TODO: All of these should through an exception if they fail to execute the command as given.

performAstEffect :: MonadIO m => AstEffect -> ExprH -> CLM m ()
performAstEffect (Apply rr) expr = do
    st <- get

    let sk = cl_kernel st
        kEnv = cl_kernel_env $ cl_session st

    sast' <- iokm2clm "Rewrite failed: " $ applyS sk (cl_cursor $ cl_session st) rr kEnv

    let commit = put (newSAST expr sast' st) >> showFocus

    if cl_corelint (cl_session st)
        then do ast' <- iokm2clm'' $ toASTS sk sast'
                liftIO (queryK (kernelS sk) ast' lintModuleT kEnv)
                >>= runKureM (\ warns -> putStrToConsole warns >> commit)
                             (\ errs  -> liftIO (deleteS sk sast') >> fail errs)
        else commit

performAstEffect (Pathfinder t) expr = do
    st <- get
    -- An extension to the Path
    iokm2clm' "Cannot find path: "
              (\ p -> do ast <- iokm2clm "Path is invalid: " $ modPathS (cl_kernel st) (cl_cursor (cl_session st)) (<> p) (cl_kernel_env $ cl_session st)
                         put $ newSAST expr ast st
                         showFocus)
              (queryS (cl_kernel st) (cl_cursor $ cl_session st) t (cl_kernel_env $ cl_session st))

performAstEffect (Direction dir) expr = do
    st <- get
    ast <- iokm2clm "Invalid move: " $ modPathS (cl_kernel st) (cl_cursor $ cl_session st) (moveLocally dir) (cl_kernel_env $ cl_session st)
    put $ newSAST expr ast st
    -- something changed, to print
    showFocus

performAstEffect BeginScope expr = do
        st <- get
        ast <- iokm2clm'' $ beginScopeS (cl_kernel st) (cl_cursor (cl_session st))
        put $ newSAST expr ast st
        showFocus

performAstEffect EndScope expr = do
        st <- get
        ast <- iokm2clm'' $ endScopeS (cl_kernel st) (cl_cursor (cl_session st))
        put $ newSAST expr ast st
        showFocus

performAstEffect (Tag tag) _ = do
        st <- get
        put (st { cl_tags = (tag, cl_cursor $ cl_session st) : cl_tags st })

performAstEffect (CorrectnessCritera q) expr = do
        st <- get
        -- TODO: Again, we may want a quiet version of the kernel_env
        liftIO (queryS (cl_kernel st) (cl_cursor $ cl_session st) q (cl_kernel_env $ cl_session st))
          >>= runKureM (\ () -> putStrToConsole $ unparseExprH expr ++ " [correct]")
                       (\ err -> fail $ unparseExprH expr ++ " [exception: " ++ err ++ "]")

-------------------------------------------------------------------------------

performShellEffect :: MonadIO m => ShellEffect -> CLM m ()
performShellEffect (SessionStateEffect f) = do
        st <- get
        opt <- liftIO (fmap Right (f st $ cl_session st) `catch` \ str -> return (Left str))
        case opt of
          Right s_st' -> do put (st { cl_session = s_st' })
                            showFocus
          Left err -> throwError err

-------------------------------------------------------------------------------

performQuery :: MonadIO m => QueryFun -> CLM m ()
performQuery (QueryString q) = do
    st <- get
    iokm2clm' "Query failed: "
              putStrToConsole
              (queryS (cl_kernel st) (cl_cursor $ cl_session st) q (cl_kernel_env $ cl_session st))

performQuery (QueryDocH q) = do
    st <- get
    let ss = cl_session st
    iokm2clm' "Query failed: "
              (liftIO . cl_render ss stdout (cl_pretty_opts ss))
              (queryS (cl_kernel st) (cl_cursor ss) (q (initPrettyC $ cl_pretty_opts ss) $ pretty ss) (cl_kernel_env ss))

performQuery (Inquiry f) = do
    st <- get
    str <- liftIO $ f st (cl_session st)
    putStrToConsole str

-- These two need to use Inquiry
performQuery (Message msg) = liftIO (putStrLn msg)
-- Explicit calls to display should work no matter what the loading state is.
performQuery Display = do
    load_st <- gets (cl_loading . cl_session)
    setLoading False
    showFocus
    setLoading load_st

-------------------------------------------------------------------------------

performMetaCommand :: MonadIO m => MetaCommand -> CLM m ()
performMetaCommand Abort  = gets cl_kernel >>= (liftIO . abortS)
performMetaCommand Resume = do st <- get
                               iokm2clm'' $ resumeS (cl_kernel st) (cl_cursor $ cl_session st)
performMetaCommand (Delete sast) = gets cl_kernel >>= iokm2clm'' . flip deleteS sast
performMetaCommand (Dump fileName _pp renderer width) = do
    st <- get
    let ss = cl_session st
    case (M.lookup (cl_pretty (ss)) pp_dictionary,lookup renderer finalRenders) of
      (Just pp, Just r) -> do doc <- iokm2clm "Bad pretty-printer or renderer option: " $
                                         queryS (cl_kernel st) (cl_cursor ss) (liftPrettyH (cl_pretty_opts ss) pp) (cl_kernel_env ss)
                              liftIO $ do h <- openFile fileName WriteMode
                                          r h ((cl_pretty_opts ss) { po_width = width }) doc
                                          hClose h
      _ -> throwError "dump: bad pretty-printer or renderer option"

performMetaCommand (LoadFile fileName) = do
       stmts   <- loadAndParseFile fileName
       load_st <- gets (cl_loading . cl_session)
       setLoading True
       evalStmts stmts `catchError` (\ err -> setLoading load_st >> throwError err)
       setLoading load_st
       putStrToConsole $ "[done, loaded " ++ show (length stmts) ++  " commands]"
       showFocus

performMetaCommand (SaveFile fileName) = do
        st <- get
        putStrToConsole $ "[saving " ++ fileName ++ "]"
        -- no checks to see if you are clobering; be careful
        liftIO $ writeFile fileName $ showGraph (cl_graph st) (cl_tags st) (SAST 0)

performMetaCommand (ImportR fileName exName) = do
        stmts <- loadAndParseFile fileName
        st    <- get
        dict' <- iokm2clm "import-rewrite failed: " (return $ importToDictionary (cl_dict st) stmts exName fileName)
        put (st {cl_dict = dict'})
        putStrToConsole $ "[done, rewrite \"" ++ exName ++ "\" imported successfully]"

-- used by performMetaCommand in the Load and Import clauses
loadAndParseFile :: MonadIO m => FilePath -> CLM m [ExprH]
loadAndParseFile fileName = do
        putStrToConsole $ "[importing " ++ fileName ++ "]"
        res <- liftIO $ try (readFile fileName)
        case res of
          Left (err :: IOException) -> throwError ("IO error: " ++ show err)
          Right str -> case parseStmtsH str of
                        Left  msg  -> throwError ("Parse failure: " ++ msg)
                        Right stmts -> return stmts

-------------------------------------------------------------------------------

putStrToConsole :: MonadIO m => String -> CLM m ()
putStrToConsole str = ifM (gets (cl_loading . cl_session))
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

cl_kernel_env  :: SessionState -> HermitMEnv
cl_kernel_env ss = mkHermitMEnv $ \ msg -> case msg of
                DebugTick    msg'      -> do
                        c <- GHC.liftIO $ tick (cl_tick ss) msg'
                        GHC.liftIO $ putStrLn $ "<" ++ show c ++ "> " ++ msg'
                DebugCore  msg' cxt core -> do
                        GHC.liftIO $ putStrLn $ "[" ++ msg' ++ "]"
                        doc :: DocH <- apply (pretty ss) (liftPrettyC (cl_pretty_opts ss) cxt) (inject core)
                        GHC.liftIO $ cl_render ss stdout (cl_pretty_opts ss) doc

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

