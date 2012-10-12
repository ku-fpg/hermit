{-# LANGUAGE FlexibleInstances, ScopedTypeVariables, GADTs, KindSignatures, TypeFamilies, DeriveDataTypeable #-}

module Language.HERMIT.Shell.Command
       ( -- * The HERMIT Command-line Shell
         commandLine
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
import Data.Dynamic
import qualified Data.Map as M
import Data.Maybe

import Language.HERMIT.Dictionary
import Language.HERMIT.Expr
import Language.HERMIT.External
import Language.HERMIT.Interp
import Language.HERMIT.Kernel.Scoped
import Language.HERMIT.Kure
import Language.HERMIT.Monad
import Language.HERMIT.PrettyPrinter
import Language.HERMIT.Primitive.Navigation
import Language.HERMIT.Primitive.Inline

-- import Language.HERMIT.Primitive.GHC

import System.Console.ANSI
import System.IO

import qualified Text.PrettyPrint.MarkedHughesPJ as PP

import System.Console.Haskeline hiding (catch)

-- There are 3 types of commands, AST effect-ful, Shell effect-ful, and Queries.

data ShellCommand :: * where
   AstEffect     :: AstEffect                -> ShellCommand
   ShellEffect   :: ShellEffect              -> ShellCommand
   QueryFun      :: QueryFun                 -> ShellCommand
   MetaCommand   :: MetaCommand              -> ShellCommand

-- | AstEffects are things that are recorded in our log and saved files.

data AstEffect
   -- | This applys a rewrite (giving a whole new lower-level AST)
   = Apply      (RewriteH Core)
   -- | This changes the current location using a computed path
   | Pathfinder (TranslateH Core Path)
   -- | This changes the currect location using directions
   | Direction  Direction
   -- | This changes the current location using a give path
   | PushFocus Path

   | BeginScope
   | EndScope
   | Tag String                 -- ^ Adding a tag
   -- | A precondition or other predicate that must not fail
   | CorrectnessCritera  (TranslateH Core ())
   deriving Typeable

instance Extern AstEffect where
    type Box AstEffect = AstEffect
    box i = i
    unbox i = i

data ShellEffect :: * where
   SessionStateEffect    :: (CommandLineState -> SessionState -> IO SessionState) -> ShellEffect
   deriving Typeable

data QueryFun :: * where
   QueryT        :: TranslateH Core String   -> QueryFun
   -- These two be can generalized into
   --  (CommandLineState -> IO String)
   Display       ::                             QueryFun
   Message       :: String                   -> QueryFun
   Inquiry       ::(CommandLineState -> SessionState -> IO String) -> QueryFun
   deriving Typeable

instance Extern QueryFun where
    type Box QueryFun = QueryFun
    box i = i
    unbox i = i

data MetaCommand
   = Resume
   | Abort
   | Dump String String String Int
   | LoadFile String  -- load a file on top of the current node
   | SaveFile String
   deriving Typeable

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

instance Extern ShellCommand where
    type Box ShellCommand = ShellCommandBox
    box = ShellCommandBox
    unbox (ShellCommandBox i) = i

interpShellCommand :: [Interp ShellCommand]
interpShellCommand =
                [ interp $ \ (ShellCommandBox cmd)       -> cmd
                , interp $ \ (IntBox i)                  -> AstEffect (PushFocus [i])
                , interp $ \ (RewriteCoreBox rr)         -> AstEffect (Apply rr)
                , interp $ \ (TranslateCorePathBox tt)   -> AstEffect (Pathfinder tt)
                , interp $ \ (StringBox str)             -> QueryFun (Message str)
                , interp $ \ (TranslateCoreStringBox tt) -> QueryFun (QueryT tt)
                , interp $ \ (TranslateCoreCheckBox tt)  -> AstEffect (CorrectnessCritera tt)
                , interp $ \ (effect :: AstEffect)       -> AstEffect effect
                , interp $ \ (effect :: ShellEffect)     -> ShellEffect effect
                , interp $ \ (query :: QueryFun)         -> QueryFun query
                , interp $ \ (meta :: MetaCommand)       -> MetaCommand meta
                ]
-- TODO: move this into the shell, it is completely specific to the way
-- the shell works. What about list, for example?

--interpKernelCommand :: [Interp KernelCommand]
--interpKernelCommand =
--             [ Interp $ \ (KernelCommandBox cmd)      -> cmd
--             ]

shell_externals :: [External]
shell_externals = map (.+ Shell)
   [
     external "resume"          Resume    -- HERMIT Kernel Exit
       [ "stops HERMIT; resumes compile" ]
   , external "abort"           Abort     -- UNIX Exit
       [ "hard UNIX-style exit; does not return to GHC; does not save" ]
   , external "display"         Display
       [ "redisplays current state" ]
   , external "left"            (Direction L)
       [ "move to the next child"]
   , external "right"           (Direction R)
       [ "move to the previous child"]
   , external "up"              (Direction U)
       [ "move to the parent"]
   , external "down"            (Direction D)
       [ "move to the first child"]
   , external "tag"             Tag
       [ "tag <label> names the current AST with a label" ]
   , external "navigate"        (SessionStateEffect $ \ _ st -> return $ st { cl_nav = True })
       [ "switch to navigate mode" ]
   , external "command-line"    (SessionStateEffect $ \ _ st -> return $ st { cl_nav = False })
       [ "switch to command line mode" ]
   , external "top"            (Direction T)
       [ "move to root of tree" ]
   , external "back"            (SessionStateEffect $ navigation Back)
       [ "go back in the derivation" ]                                          .+ VersionControl
   , external "log"             (Inquiry showDerivationTree)
       [ "go back in the derivation" ]                                          .+ VersionControl
   , external "step"            (SessionStateEffect $ navigation Step)
       [ "step forward in the derivation" ]                                     .+ VersionControl
   , external "goto"            (SessionStateEffect . navigation . Goto)
       [ "goto a specific step in the derivation" ]                             .+ VersionControl
   , external "goto"            (SessionStateEffect . navigation . GotoTag)
       [ "goto a named step in the derivation" ]
   , external "setpp"           (\ pp -> SessionStateEffect $ \ _ st ->
       case M.lookup pp pp_dictionary of
         Nothing -> do
            putStrLn $ "List of Pretty Printers: " ++ intercalate ", " (M.keys pp_dictionary)
            return st
         Just _ -> return $ st { cl_pretty = pp })
       [ "set the pretty printer"
       , "use 'setpp ls' to list available pretty printers" ]
   , external "set-renderer"    changeRenderer
       [ "set the output renderer mode"]
   , external "set-renderer"    showRenderers
       [ "set the output renderer mode"]
   , external "dump"    Dump
       [ "dump <filename> <pretty-printer> <renderer> <width>"]
   , external "set-width"   (\ n -> SessionStateEffect $ \ _ st -> return $ st { cl_width = n })
       ["set the width of the screen"]
   , external "set-pp-expr-type"
                (\ str -> SessionStateEffect $ \ _ st -> case reads str :: [(ShowOption,String)] of
                                                 [(opt,"")] -> return $ st { cl_pretty_opts =
                                                                                 (cl_pretty_opts st) { po_exprTypes = opt }
                                                                           }
                                                 _ -> return st)
       ["set how to show expression-level types (Show|Abstact|Omit)"]
   , external "{"   BeginScope
       ["push current lens onto a stack"]       -- tag as internal
   , external "}"   EndScope
       ["pop a lens off a stack"]               -- tag as internal
   , external "load"  LoadFile
       ["load <filename> : load a file of commands into the current derivation"]
   , external "save"  SaveFile
       ["save <filename> : save the current complete derivation into a file"]
   ]

showRenderers :: QueryFun
showRenderers = Message $ "set-renderer " ++ show (map fst finalRenders)

changeRenderer :: String -> ShellEffect
changeRenderer renderer = SessionStateEffect $ \ _ st ->
        case lookup renderer finalRenders of
          Nothing -> return st          -- should fail with message
          Just r  -> return $ st { cl_render = r }

----------------------------------------------------------------------------------

catch :: IO a -> (String -> IO a) -> IO a
catch = catchJust (\ (err :: IOException) -> return (show err))

pretty :: SessionState -> PrettyH Core
pretty ss = case M.lookup (cl_pretty ss) pp_dictionary of
                Just pp -> pp (cl_pretty_opts ss)
                Nothing -> pure (PP.text $ "<<no pretty printer for " ++ cl_pretty ss ++ ">>")

showFocus :: MonadIO m => CLM m ()
showFocus = do
    st <- get
    -- No not show focus while loading
    ifM (gets (cl_loading . cl_session))
        (return ())
        (iokm2clm' "Rendering error: "
                   (liftIO . cl_render (cl_session st) stdout (cl_pretty_opts $ cl_session st))
                   (queryS (cl_kernel st) (cl_cursor $ cl_session st) (pretty $ cl_session st) (cl_kernel_env $ cl_session st))
        )

-------------------------------------------------------------------------------

type CLM m a = ErrorT String (StateT CommandLineState m) a

-- TODO: Come up with names for these, and/or better characterise these abstractions.
iokm2clm' :: MonadIO m => String -> (a -> CLM m b) -> IO (KureM a) -> CLM m b
iokm2clm' msg ret m = liftIO m >>= runKureM ret (throwError . (msg ++))

iokm2clm :: MonadIO m => String -> IO (KureM a) -> CLM m a
iokm2clm msg = iokm2clm' msg return

data CommandLineState = CommandLineState
        { cl_graph       :: [(SAST,ExprH,SAST)]
        , cl_tags        :: [(String,SAST)]
        -- these two should be in a reader
        , cl_dict        :: Dictionary
        , cl_kernel      :: ScopedKernel
        -- and the session state (perhaps in a seperate state?)
        , cl_session     :: SessionState
        }

newSAST :: ExprH -> SAST -> CommandLineState -> CommandLineState
newSAST expr sast st = st { cl_session = (cl_session st) { cl_cursor = sast }
                          , cl_graph = (cl_cursor (cl_session st), expr, sast) : cl_graph st
                          }

-- Session-local issues; things that are never saved.
data SessionState = SessionState
        { cl_cursor      :: SAST              -- ^ the current AST
        , cl_pretty      :: String           -- ^ which pretty printer to use
        , cl_pretty_opts :: PrettyOptions -- ^ The options for the pretty printer
        , cl_render      :: Handle -> PrettyOptions -> DocH -> IO ()   -- ^ the way of outputing to the screen
        , cl_width       :: Int                 -- ^ how wide is the screen?
        , cl_nav         :: Bool        -- ^ keyboard input the the nav panel
        , cl_loading     :: Bool        -- ^ if loading a file
        , cl_tick        :: TVar (M.Map String Int)     -- ^ The list of ticked messages
        }

-------------------------------------------------------------------------------

data CompletionType = ConsiderC -- complete with possible arguments to consider
                    | InlineC   -- complete with names that can be inlined
                    | CommandC  -- complete using dictionary commands (default)
                    | AmbiguousC [CompletionType]  -- completionType function needs to be more specific
    deriving (Show)

-- todo: reverse rPrev and parse it, to better figure out what possiblities are in context?
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

completionQuery :: CommandLineState -> CompletionType -> IO (TranslateH Core [String])
completionQuery _ ConsiderC = return $ considerTargets >>^ ((++ map fst considerables) . map ('\'':))
completionQuery _ InlineC   = return $ inlineTargets   >>^ map ('\'':)
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
    mcls <- queryS (cl_kernel st) (cl_cursor (cl_session st)) targetQuery (cl_kernel_env (cl_session st))
    cl <- runKureM return fail mcls -- TO DO: probably shouldn't use fail here.
    return $ (map simpleCompletion . nub . filter (so_far `isPrefixOf`)) cl

-- | The first argument is a list of files to load.
commandLine :: [String] -> Behavior -> GHC.ModGuts -> GHC.CoreM GHC.ModGuts
commandLine filesToLoad behavior modGuts = do
    let dict = dictionary $ all_externals shell_externals
    let ws_complete = " ()"

    let startup = do
            modify $ \st -> st { cl_session = (cl_session st) { cl_loading = True } }
            sequence_ [ performMetaCommand $ case fileName of
                         "abort"  -> Abort
                         "resume" -> Resume
                         _        -> LoadFile fileName
                      | fileName <- reverse filesToLoad
                      , not (null fileName)
                      ] `ourCatch` \ msg -> liftIO . putStrLn $ "Booting Failure: " ++ msg
            modify $ \st -> st { cl_session = (cl_session st) { cl_loading = False } }

    var <- GHC.liftIO $ atomically $ newTVar M.empty

    flip scopedKernel modGuts $ \ skernel sast -> do

        let sessionState = SessionState sast "clean" def unicodeConsole 80 False False var
            shellState = CommandLineState [] [] dict skernel sessionState

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

ourCatch :: (MonadIO n) => CLM IO () -> (String -> CLM n ()) -> CLM n ()
ourCatch m failure = do
                st <- get
                (res,st') <- liftIO $ runStateT (runErrorT m) st
                put st'
                case res of
                  Left msg -> failure msg
                  Right () -> return ()



evalStmts :: (MonadIO m) => [StmtH ExprH] -> CLM m ()
evalStmts = mapM_ evalExpr . scopes
    where scopes :: [StmtH ExprH] -> [ExprH]
          scopes [] = []
          scopes (ExprH e:ss) = e : scopes ss
          scopes (ScopeH s:ss) = (CmdName "{" : scopes s) ++ [CmdName "}"] ++ scopes ss


evalExpr :: (MonadIO m) => ExprH -> CLM m ()
evalExpr expr = do
    dict <- gets cl_dict
    case interpExprH dict interpShellCommand expr of
      Left msg  -> throwError msg
      Right cmd -> case cmd of
                     AstEffect effect   -> performAstEffect effect expr
                     ShellEffect effect -> performShellEffect effect
                     QueryFun query     -> performQuery query
                     MetaCommand meta   -> performMetaCommand meta

-------------------------------------------------------------------------------

-- TODO: This can be refactored. We always showFocus. Also, Perhaps return a modifier, not ()
--   UPDATE: Not true.  We don't always showFocus.
-- TODO: All of these should through an exception if they fail to execute the command as given.

performAstEffect :: MonadIO m => AstEffect -> ExprH -> CLM m ()
performAstEffect (Apply rr) expr = do
    st <- get
    iokm2clm' "Rewrite failed: "
              (\ ast' -> put (newSAST expr ast' st) >> showFocus)
              (applyS (cl_kernel st) (cl_cursor $ cl_session st) rr (cl_kernel_env $ cl_session st))

performAstEffect (Pathfinder t) expr = do
    st <- get
    -- An extension to the Path
    iokm2clm' "Cannot find path: "
              (\ p -> do ast <- iokm2clm "Path is invalid: " $ modPathS (cl_kernel st) (cl_cursor (cl_session st)) (extendLocalPath p) (cl_kernel_env $ cl_session st)
                         put $ newSAST expr ast st
                         showFocus)
              (queryS (cl_kernel st) (cl_cursor $ cl_session st) t (cl_kernel_env $ cl_session st))

performAstEffect (Direction dir) expr = do
    st <- get
    -- This seems unnecassary.  But if you restore it, note that it needs editing so that it doesn't print if we're loading a file.
    -- child_count <- iokm2clm "Could not compute number of children:" $ queryS (cl_kernel st) (cl_cursor (cl_session st)) numChildrenT (cl_kernel_env (cl_session st))
    -- liftIO $ print (child_count, dir)
    ast <- iokm2clm "Invalid move: " $ modPathS (cl_kernel st) (cl_cursor $ cl_session st) (moveLocally dir) (cl_kernel_env $ cl_session st)
    put $ newSAST expr ast st
    -- something changed, to print
    showFocus

performAstEffect (PushFocus p) expr = do
    st <- get
    ast <- iokm2clm "Invalid push: " $ modPathS (cl_kernel st) (cl_cursor $ cl_session st) (extendLocalPath p) (cl_kernel_env $ cl_session st)
    put $ newSAST expr ast st
    showFocus

performAstEffect BeginScope expr = do
        st <- get
        ast <- liftIO $ beginScopeS (cl_kernel st) (cl_cursor (cl_session st))
        put $ newSAST expr ast st
        showFocus

performAstEffect EndScope expr = do
        st <- get
        ast <- liftIO $ endScopeS (cl_kernel st) (cl_cursor (cl_session st))
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
        -- correctness <- liftIO (try $ queryS (cl_kernel st) (cl_cursor (cl_session st)) q)
        -- case correctness of
        --   Right ()  -> do putStrToConsole $ unparseExprH expr ++ " [correct]"
        --   Left (err :: IOException)
        --            -> fail $ unparseExprH expr ++ " [exception: " ++ show err ++ "]"


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
performQuery (QueryT q) = do
    st <- get
    iokm2clm' "Query failed: "
              putStrToConsole
              (queryS (cl_kernel st) (cl_cursor $ cl_session st) q (cl_kernel_env $ cl_session st))

performQuery (Inquiry f) = do
    st <- get
    str <- liftIO $ f st (cl_session st)
    putStrToConsole str

-- These two need to use Inquiry
performQuery (Message msg) = liftIO (putStrLn msg)
performQuery Display = showFocus
  -- do
  --   st <- get
  --   liftIO $ do
  --       ps <- pathS (cl_kernel st) (cl_cursor (cl_session st))
  --       putStrLn $ "Paths: " ++ show ps
  --       print ("Graph",cl_graph st)
  --       print ("This",cl_cursor (cl_session st))

-------------------------------------------------------------------------------

performMetaCommand :: MonadIO m => MetaCommand -> CLM m ()
performMetaCommand Abort  = gets cl_kernel >>= (liftIO . abortS)
performMetaCommand Resume = do st <- get
                               liftIO $ resumeS (cl_kernel st) (cl_cursor $ cl_session st)
performMetaCommand (Dump fileName _pp renderer width) = do
    st <- get
    case (M.lookup (cl_pretty (cl_session st)) pp_dictionary,lookup renderer finalRenders) of
        (Just pp, Just r) -> do doc <- iokm2clm "Bad pretty-printer or renderer option: " $
                                           queryS (cl_kernel st) (cl_cursor $ cl_session st) (pp (cl_pretty_opts $ cl_session st)) (cl_kernel_env $ cl_session st)
                                liftIO $ do h <- openFile fileName WriteMode
                                            r h ((cl_pretty_opts $ cl_session st) { po_width = width }) doc
                                            hClose h
        _ -> throwError "dump: bad pretty-printer or renderer option"
performMetaCommand (LoadFile fileName) = do
        putStrToConsole $ "[loading " ++ fileName ++ "]"
        res <- liftIO $ try (readFile fileName)
        case res of
          Right str -> case parseStmtsH (normalize str) of
                        Left  msg  -> throwError ("Parse failure: " ++ msg)
                        Right stmts -> do
                            load_st <- gets (cl_loading . cl_session)
                            modify $ \st -> st { cl_session = (cl_session st) { cl_loading = True } }
                            evalStmts stmts `catchError` (\ err -> do
                                    modify $ \ st -> st { cl_session = (cl_session st) { cl_loading = load_st } }
                                    throwError err)
                            modify $ \st -> st { cl_session = (cl_session st) { cl_loading = load_st } }
                            putStrToConsole $ "[done, loaded " ++ show (numStmtsH stmts) ++  " commands]" -- TODO: This is better than saying "N", but not very robust.
                            showFocus
          Left (err :: IOException) -> throwError ("IO error: " ++ show err)
  where
   normalize = unlines
             . map (++ ";")     -- HACK!
             . map rmComment
             . lines
   rmComment []     = []
   rmComment xs     | "--" `isPrefixOf` xs = [] -- we need a real parser and lexer here!
   rmComment (x:xs) = x : rmComment xs

performMetaCommand (SaveFile fileName) = do
        st <- get
        putStrToConsole $ "[saving " ++ fileName ++ "]"
        -- no checks to see if you are clobering; be careful
        liftIO $ writeFile fileName $ showGraph (cl_graph st) (cl_tags st) (SAST 0)


-------------------------------------------------------------------------------

putStrToConsole :: MonadIO m => String -> CLM m ()
putStrToConsole str = ifM (gets (cl_loading . cl_session))
                          (return ())
                          (liftIO $ putStrLn str)

-------------------------------------------------------------------------------

newtype UnicodeTerminal = UnicodeTerminal (Handle -> Maybe Path -> IO ())

instance RenderSpecial UnicodeTerminal where
        renderSpecial sym = UnicodeTerminal $ \ h _ -> hPutStr h [ch]
                where (Unicode ch) = renderSpecial sym

instance Monoid UnicodeTerminal where
        mempty = UnicodeTerminal $ \ _ _ -> return ()
        mappend (UnicodeTerminal f1) (UnicodeTerminal f2) = UnicodeTerminal $ \ h p -> f1 h p >> f2 h p

finalRenders :: [(String,Handle -> PrettyOptions -> DocH -> IO ())]
finalRenders =
        [ ("unicode-terminal", unicodeConsole)
        ] ++ coreRenders

unicodeConsole :: Handle -> PrettyOptions -> DocH -> IO ()
unicodeConsole h w doc = do
    let (UnicodeTerminal prty) = renderCode w doc
    prty h Nothing


instance RenderCode UnicodeTerminal where
        rPutStr txt  = UnicodeTerminal $ \ h _ -> hPutStr h txt

        rDoHighlight _ [] = UnicodeTerminal $ \ h _ -> hSetSGR h [Reset]
        rDoHighlight _ (Color col:_) = UnicodeTerminal $ \ h _ -> do
                hSetSGR h [ Reset ]
                hSetSGR h $ case col of
                        KeywordColor -> [ SetConsoleIntensity BoldIntensity
                                        , SetColor Foreground Dull Blue
                                        ]
                        SyntaxColor  -> [ SetColor Foreground Dull Red ]
                        VarColor     -> []   -- as is
                        TypeColor    -> [ SetColor Foreground Dull Green ]
                        LitColor     -> [ SetColor Foreground Dull Cyan ]
        rDoHighlight o (_:rest) = rDoHighlight o rest
        rEnd = UnicodeTerminal $ \ h _ -> hPutStrLn h ""

--------------------------------------------------------

navigation :: Navigation -> CommandLineState -> SessionState -> IO SessionState
navigation whereTo st sess_st =
    case whereTo of
      Goto n -> do
           all_nds <- listS (cl_kernel st)
           if SAST n `elem` all_nds
              then return $ sess_st { cl_cursor = SAST n }
              else fail $ "Can not find AST #" ++ show n
      GotoTag tag -> case lookup tag (cl_tags st) of
                       Just sast -> return $ sess_st { cl_cursor = sast }
                       Nothing   -> fail $ "Can not find tag " ++ show tag
      Step -> do
           let ns = [ edge | edge@(s,_,_) <- cl_graph st, s == cl_cursor (cl_session st) ]
           case ns of
             [] -> fail "Cannot step forward (no more steps)"
             [(_,cmd,d) ] -> do
                           putStrLn $ "step : " ++ unparseExprH cmd
                           return $ sess_st { cl_cursor = d }
             _ -> fail "Cannot step forward (multiple choices)"
      Back -> do
           let ns = [ edge | edge@(_,_,d) <- cl_graph st, d == cl_cursor (cl_session st) ]
           case ns of
             []         -> fail "Cannot step backwards (no more steps)"
             [(s,cmd,_) ] -> do
                           putStrLn $ "back, unstepping : " ++ unparseExprH cmd
                           return $ sess_st { cl_cursor = s }
             _          -> fail "Cannot step backwards (multiple choices, impossible!)"

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


showDerivationTree :: CommandLineState -> SessionState -> IO String
showDerivationTree st ss = return $ unlines $ showRefactorTrail graph tags 0 me
  where
          graph = [ (a,[unparseExprH b],c) | (SAST a,b,SAST c) <- cl_graph st ]
          tags  = [ (n,nm) | (nm,SAST n) <- cl_tags st ]
          SAST me = cl_cursor ss

showRefactorTrail :: (Eq a, Show a) => [(a,[String],a)] -> [(a,String)] -> a -> a -> [String]
showRefactorTrail db tags a me =
        case [ (b,c) | (a0,b,c) <- db, a == a0 ] of
           [] -> [show' 3 a ++ " " ++ dot ++ tags_txt]
           ((b,c):bs) ->
                      [show' 3 a ++ " " ++ dot ++ (if not (null bs) then "->" else "") ++ tags_txt ] ++
                      ["    " ++ "| " ++ txt | txt <- b ] ++
                      showRefactorTrail db tags c me ++
                      if null bs
                      then []
                      else [] :
                          showRefactorTrail [ (a',b',c') | (a',b',c') <- db
                                                          , not (a == a' && c == c')
                                                          ]  tags a me

  where
          dot = if a == me then "*" else "o"
          show' n x = replicate (n - length (show a)) ' ' ++ show x
          tags_txt = concat [ ' ' : txt
                            | (n,txt) <- tags
                            , n == a
                            ]


showGraph :: [(SAST,ExprH,SAST)] -> [(String,SAST)] -> SAST -> String
showGraph graph tags this@(SAST n) =
        (if length paths > 1 then "tag " ++ show n ++ "\n" else "") ++
        concat (intercalate
                ["goto " ++ show n ++ "\n"]
                [ [ unparseExprH b ++ "\n" ++ showGraph graph tags c ]
                | (b,c) <- paths
                ])
  where
          paths = [ (b,c) | (a,b,c) <- graph, a == this ]

----------------------------------------------------------------------------------------------

cl_kernel_env  :: SessionState -> HermitMEnv
cl_kernel_env ss = mkHermitMEnv $ \ msg -> case msg of
                DebugTick    msg'      -> do
                        c <- GHC.liftIO $ tick (cl_tick ss) msg'
                        GHC.liftIO $ putStrLn $ "<" ++ show c ++ "> " ++ msg'
                DebugCore  msg' cxt core -> do
                        GHC.liftIO $ putStrLn $ "[" ++ msg' ++ "]"
                        doc :: DocH <- apply (pretty ss) cxt core
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

