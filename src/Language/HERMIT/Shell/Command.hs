{-# LANGUAGE FlexibleInstances, ScopedTypeVariables, GADTs, KindSignatures, TypeFamilies, DeriveDataTypeable #-}

module Language.HERMIT.Shell.Command where

import qualified GhcPlugins as GHC

import Control.Applicative
import Control.Exception.Base hiding (catch)
import Control.Monad.State

import Data.Char
import Data.Monoid
import Data.List (intercalate, isPrefixOf)
import Data.Default (def)
import Data.Dynamic
import qualified Data.Map as M
import Data.Maybe

import Language.HERMIT.HermitExpr
import Language.HERMIT.External
import Language.HERMIT.Interp
import Language.HERMIT.HermitKure
import Language.HERMIT.Kernel.Scoped
import Language.HERMIT.PrettyPrinter
import Language.HERMIT.Dictionary

import Prelude hiding (catch)

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

data AstEffect :: * where
   -- | This applys a rewrite (giving a whole new lower-level AST)
   Apply        :: RewriteH Core            -> AstEffect
   -- | This changes the current location using a computed path
   Pathfinder   :: TranslateH Core Path     -> AstEffect
   -- | This changes the currect location using directions
   Direction     :: Direction                -> AstEffect
   -- | This changes the current location using a give path
   PushFocus     :: Path                     -> AstEffect
   -- |
--   ShellState'  :: (CommandLineState -> IO CommandLineState) -> AstEffect
   BeginScope    :: AstEffect
   EndScope      :: AstEffect
   deriving Typeable

instance Extern AstEffect where
    type Box AstEffect = AstEffect
    box i = i
    unbox i = i

data ShellEffect :: * where

   -- This should only be the shell's state part, no the whole state
   -- call SessionState
   SessionStateEffect    :: (SessionState -> IO SessionState) -> ShellEffect
   deriving Typeable

data QueryFun :: * where
   Query         :: TranslateH Core String   -> QueryFun  -- strange stuff

   -- These two be can generalized into
   --  (CommandLineState -> IO String)
   Status        ::                             QueryFun
   Message       :: String                   -> QueryFun
   deriving Typeable

instance Extern QueryFun where
    type Box QueryFun = QueryFun
    box i = i
    unbox i = i

data MetaCommand :: * where
   Resume       ::                             MetaCommand
   Abort        ::                             MetaCommand
   Dump          :: String -> String -> String -> Int -> MetaCommand
   deriving Typeable

instance Extern MetaCommand where
    type Box MetaCommand = MetaCommand
    box i = i
    unbox i = i

data Direction = L | R | U | D | T
        deriving Show

data ShellCommandBox = ShellCommandBox ShellCommand deriving Typeable

instance Extern ShellEffect where
    type Box ShellEffect = ShellEffect
    box i = i
    unbox i = i

instance Extern ShellCommand where
    type Box ShellCommand = ShellCommandBox
    box i = ShellCommandBox i
    unbox (ShellCommandBox i) = i

interpShellCommand :: [Interp ShellCommand]
interpShellCommand =
                [ Interp $ \ (ShellCommandBox cmd)       -> cmd
                , Interp $ \ (IntBox i)                  -> AstEffect $ PushFocus [i]
                , Interp $ \ (RewriteCoreBox rr)         -> AstEffect $ Apply rr
                , Interp $ \ (TranslateCorePathBox tt)   -> AstEffect $ Pathfinder tt
                , Interp $ \ (StringBox str)             -> QueryFun $ Message str
                , Interp $ \ (TranslateCoreStringBox tt) -> QueryFun $ Query tt
                , Interp $ \ (effect :: AstEffect)       -> AstEffect $ effect
                , Interp $ \ (effect :: ShellEffect)     -> ShellEffect $ effect
                , Interp $ \ (query :: QueryFun)        -> QueryFun $ query
                , Interp $ \ (meta :: MetaCommand)     -> MetaCommand $ meta
                ]
-- TODO: move this into the shell, it is completely specific to the way
-- the shell works. What about list, for example?

--interpKernelCommand :: [Interp KernelCommand]
--interpKernelCommand =
--             [ Interp $ \ (KernelCommandBox cmd)      -> cmd
--             ]

shell_externals :: [External]
shell_externals = map (.+ Shell) $
   [
     external "resume"          Resume    -- HERMIT Kernel Exit
       [ "stops HERMIT; resumes compile" ]
   , external "quit"           Abort     -- UNIX Exit
       [ "hard UNIX-style exit; does not return to GHC; does not save" ]
   , external "status"          Status
       [ "redisplays current state" ]
   , external "left"            (Direction L)
       [ "move to the next child"]
   , external "right"           (Direction R)
       [ "move to the previous child"]
   , external "up"              (Direction U)
       [ "move to the parent"]
   , external "down"            (Direction D)
       [ "move to the first child"]
   , external "esc-D"            (Direction L)
       [ "move to the next child"]
   , external "esc-C"           (Direction R)
       [ "move to the previous child"]
   , external "esc-A"              (Direction U)
       [ "move to the parent"]
   , external "esc-B"            (Direction D)
       [ "move to the first child"]
   , external ":navigate"        (SessionStateEffect $ \ st -> return $ st { cl_nav = True })
       [ "switch to navigate mode" ]
   , external ":command-line"    (SessionStateEffect $ \ st -> return $ st { cl_nav = False })
       [ "switch to command line mode" ]
   , external "top"            (Direction T)
       [ "move to root of tree" ]
   , external "setpp"           (\ pp -> SessionStateEffect $ \ st -> do
       case M.lookup pp pp_dictionary of
         Nothing -> do
            liftIO $ putStrLn $ "List of Pretty Printers: " ++ intercalate ", " (M.keys pp_dictionary)
            return st
         Just v -> return $ st { cl_pretty = pp })
       [ "set the pretty printer"
       , "use 'setpp ls' to list available pretty printers" ]
   , external "set-renderer"    changeRenderer
       [ "set the output renderer mode"]
   , external "set-renderer"    showRenderers
       [ "set the output renderer mode"]
   , external "dump"    Dump
       [ "dump <filename> <pretty-printer> <renderer> <width>"]
   , external "set-width"   (\ n -> SessionStateEffect $ \ st -> return $ st { cl_width = n })
       ["set the width of the screen"]
   , external "set-pp-expr-type"
                (\ str -> SessionStateEffect $ \ st -> case reads str :: [(ShowOption,String)] of
                                                 [(opt,"")] -> return $ st { cl_pretty_opts =
                                                                                 (cl_pretty_opts st) { po_exprTypes = opt }
                                                                           }
                                                 _ -> return $ st)
       ["set how to show expression-level types (Show|Abstact|Omit)"]
   , external "{"   BeginScope
       ["push current lens onto a stack"]       -- tag as internal
   , external "}"   EndScope
       ["pop a lens off a stack"]               -- tag as internal
--   , external "include" (\ (fileName :: String) -> ShellState' $ \ st -> includeFile fileName st)
--        ["include <filename>: includes a shell command file"]
   ]

showRenderers :: QueryFun
showRenderers = Message $ "set-renderer " ++ show (map fst finalRenders)

changeRenderer :: String -> ShellEffect
changeRenderer renderer = SessionStateEffect $ \ st ->
        case lookup renderer finalRenders of
          Nothing -> return st          -- should fail with message
          Just r  -> return $ st { cl_render = r }

----------------------------------------------------------------------------------

includeFile :: String -> CommandLineState -> IO CommandLineState
includeFile fileName st = do
        putStrLn $ "[including " ++ fileName ++ "]"
        res <- try (readFile fileName)
        case res of
          Right str -> case parseStmtsH (normalize str) of
                        Left  msg  -> putStrLn ("parse failure: " ++ msg) >> return st
                        Right stmts -> execStateT (evalStmts stmts) st
          Left (err :: IOException) -> putStrLn ("IO error: " ++ show err) >> return st
  where
   normalize = unlines
             . map (++ ";")     -- HACK!
             . map (rmComment)
             . lines
   rmComment []     = []
   rmComment xs     | "--" `isPrefixOf` xs = [] -- we need a real parser and lexer here!
   rmComment (x:xs) = x : rmComment xs

----------------------------------------------------------------------------------

catch :: IO a -> (String -> IO a) -> IO a
catch = catchJust (\ (err :: IOException) -> return (show err))

pretty :: CommandLineState -> PrettyH Core
pretty st = case M.lookup (cl_pretty (cl_session st)) pp_dictionary of
                Just pp -> pp (cl_pretty_opts (cl_session st))
                Nothing -> pure (PP.text $ "<<no pretty printer for " ++ cl_pretty (cl_session st) ++ ">>")

showFocus :: (MonadIO m) => CLM m ()
showFocus = do
    st <- get
    liftIO ((do
        doc <- queryS (cl_kernel st) (cl_cursor st) (pretty st)
        cl_render (cl_session st) stdout (cl_pretty_opts (cl_session st)) doc)
          `catch` \ msg -> putStrLn $ "Error thrown: " ++ msg)

-------------------------------------------------------------------------------

newtype ScopePath = ScopePath [Int]

emptyScopePath :: ScopePath
emptyScopePath = ScopePath []

concatScopePaths :: [ScopePath] -> ScopePath
concatScopePaths = ScopePath . foldr (\ (ScopePath ns) ms -> ns ++ ms) []

scopePath2Path :: ScopePath -> Path
scopePath2Path (ScopePath p) = reverse p

path2ScopePath :: Path -> ScopePath
path2ScopePath p = ScopePath (reverse p)

moveLocally :: Direction -> ScopePath -> ScopePath
moveLocally D (ScopePath ns)             = ScopePath (0:ns)
moveLocally U (ScopePath (_:ns))         = ScopePath ns
moveLocally L (ScopePath (n:ns)) | n > 0 = ScopePath ((n-1):ns)
moveLocally R (ScopePath (n:ns))         = ScopePath ((n+1):ns)
moveLocally T _                          = ScopePath []
moveLocally _ p                          = p

-- ascendDescentPath :: DescentPath -> Maybe (Int, DescentPath)
-- ascendDescentPath (DescentPath [])     = Nothing
-- ascendDescentPath (DescentPath (n:ns)) = Just (n,ns)

-- descendDescentPath :: Int -> DescentPath -> DescentPath

-- scopePathL :: ScopePath -> LensH Core Core
-- scopePathL = pathL . reverse

-------------------------------------------------------------------------------

type CLM m a = StateT CommandLineState m a

data CommandLineState = CommandLineState
        { cl_cursor      :: SAST              -- ^ the current AST
        , cl_graph       :: [(SAST,ExprH,SAST)]
        -- these two should be in a reader
        , cl_dict        :: M.Map String [Dynamic]
        , cl_kernel       :: ScopedKernel
        -- and the session state
        , cl_session      :: SessionState
        }

newSAST :: ExprH -> SAST -> CommandLineState -> CommandLineState
newSAST expr sast st = st { cl_cursor = sast
                          , cl_graph = (cl_cursor st, expr, sast) : cl_graph st
                          }

-- Session-local issues; things that are never saved.
data SessionState = SessionState
        { cl_pretty      :: String           -- ^ which pretty printer to use
        , cl_pretty_opts :: PrettyOptions -- ^ The options for the pretty printer
        , cl_render      :: Handle -> PrettyOptions -> DocH -> IO ()   -- ^ the way of outputing to the screen
        , cl_width       :: Int                 -- ^ how wide is the screen?
        , cl_nav         :: Bool
        }



-------------------------------------------------------------------------------

commandLine :: Behavior -> GHC.ModGuts -> GHC.CoreM GHC.ModGuts
commandLine behavior modGuts = do
    GHC.liftIO $ print (length (GHC.mg_rules modGuts))
    let dict = dictionary $ all_externals shell_externals modGuts
    let ws_complete = " ()"
    let do_complete _ so_far =
            return [ simpleCompletion cmd
                   | cmd <- M.keys dict
                   , so_far `isPrefixOf` cmd
                   ]


    flip scopedKernel modGuts $ \ skernel sast -> do

        let sessionState = SessionState "clean" def unicodeConsole 80 False
            shellState = CommandLineState sast [] dict skernel sessionState

        runInputTBehavior behavior
                (setComplete (completeWordWithPrev Nothing ws_complete do_complete) defaultSettings)
                (evalStateT (showFocus >> loop) shellState)

        return ()

loop :: (MonadIO m, m ~ InputT IO) => CLM m ()
loop = do
    st <- get
--    liftIO $ print (cl_pretty st, cl_cursor st)
    maybeLine <- if cl_nav (cl_session st)
                 then liftIO $ getNavCmd
                 else lift $ getInputLine "hermit> "
    case maybeLine of
        Nothing             -> performMetaCommand Resume
        Just ('-':'-':_msg) -> loop
        Just line           ->
            if all isSpace line
            then loop
            else do case parseStmtsH line of
                        Left  msg   -> liftIO $ putStrLn ("parse failure: " ++ msg)
                        Right stmts -> evalStmts stmts
                    loop

evalStmts :: (MonadIO m) => [StmtH ExprH] -> CLM m ()
evalStmts = mapM_ evalExpr . scopes
    where scopes :: [StmtH ExprH] -> [ExprH]
          scopes [] = []
          scopes (ExprH e:ss) = e : scopes ss
          scopes (ScopeH s:ss) = (CmdName "{" : scopes s) ++ [CmdName "}"] ++ scopes ss

evalExpr :: (MonadIO m) => ExprH -> CLM m ()
evalExpr expr = do
    dict <- gets cl_dict
    case interpExprH
                dict
                interpShellCommand
                expr of
            Left msg  -> liftIO $ putStrLn msg
            Right cmd -> do
                liftIO (putStrLn $ "doing : " ++ show expr)
                case cmd of
                  AstEffect effect   -> performAstEffect effect expr
                  ShellEffect effect -> performShellEffect effect
                  QueryFun query     -> performQuery query
                  MetaCommand meta   -> performMetaCommand meta

-------------------------------------------------------------------------------

-- TODO: This can be refactored. We always showFocus. Also, Perhaps return a modifier, not ()

performAstEffect :: (MonadIO m) => AstEffect -> ExprH -> CLM m ()
performAstEffect (Apply rr) expr = do
    st <- get
    -- something changed (you've applied)
    ast' <- liftIO $ (do ast' <- applyS (cl_kernel st) (cl_cursor st) rr
                         return $ Right ast')
                           `catch` \ msg -> return $ Left $ "Error thrown: " ++ msg
    either (liftIO . putStrLn) (\ast' -> do put $ newSAST expr ast' st
                                            showFocus
                                            return ()) ast'
performAstEffect (Pathfinder t) expr = do
    st <- get
    -- An extension to the Path
    ast <- liftIO $ do
        p <- queryS (cl_kernel st) (cl_cursor st) t `catch` (\ msg -> (putStrLn $ "Error thrown: " ++ msg) >> return [])
        modPathS (cl_kernel st) (cl_cursor st) (++ p)
    put $ newSAST expr ast st
    showFocus
performAstEffect (Direction dir) expr = do
    st <- get
    ast <- liftIO $ do
        child_count <- queryS (cl_kernel st) (cl_cursor st) numChildrenT
        print (child_count, dir)
        modPathS (cl_kernel st) (cl_cursor st) (scopePath2Path . moveLocally dir . path2ScopePath)
    put $ newSAST expr ast st
    -- something changed, to print
    showFocus
--performAstEffect (ShellState' f) = get >>= liftIO . f >>= put >> showFocus
performAstEffect (PushFocus ls) expr = do
    st <- get
    ast <- liftIO $ modPathS (cl_kernel st) (cl_cursor st) (++ ls)
    put $ newSAST expr ast st
    showFocus
performAstEffect BeginScope expr = do
        st <- get
        ast <- liftIO $ beginScopeS (cl_kernel st) (cl_cursor st)
        put $ newSAST expr ast st
        showFocus
performAstEffect EndScope expr = do
        st <- get
        ast <- liftIO $ endScopeS (cl_kernel st) (cl_cursor st)
        put $ newSAST expr ast st
        showFocus

-------------------------------------------------------------------------------

performShellEffect :: (MonadIO m) => ShellEffect -> CLM m ()
performShellEffect (SessionStateEffect f) = do
        st <- get
        s_st' <- liftIO (f (cl_session st))
        put (st { cl_session = s_st' })
        showFocus

-------------------------------------------------------------------------------

performQuery :: (MonadIO m) => QueryFun -> CLM m ()
performQuery (Query q) = do
    st <- get
    -- something changed, to print
    liftIO ((queryS (cl_kernel st) (cl_cursor st) q >>= putStrLn)
              `catch` \ msg -> putStrLn $ "Error thrown: " ++ msg)
performQuery Status = do
    st <- get
    liftIO $ do
        ps <- pathS (cl_kernel st) (cl_cursor st)
        putStrLn $ "Paths: " ++ show ps
    showFocus


performQuery (Message msg) = liftIO (putStrLn msg)

-------------------------------------------------------------------------------

performMetaCommand :: (MonadIO m) => MetaCommand -> CLM m ()
performMetaCommand Abort  = gets cl_kernel >>= (liftIO . abortS)
performMetaCommand Resume = get >>= \st -> liftIO $ resumeS (cl_kernel st) (cl_cursor st)
performMetaCommand (Dump fileName _pp renderer w) = do
    st <- get
    liftIO $ case (M.lookup (cl_pretty (cl_session st)) pp_dictionary,lookup renderer finalRenders) of
        (Just pp, Just r) -> do
            doc <- queryS (cl_kernel st) (cl_cursor st) (pp (cl_pretty_opts (cl_session st)))
            h <- openFile fileName WriteMode
            r h (cl_pretty_opts (cl_session st)) doc
            hClose h
        _ -> do putStrLn "dump: bad pretty-printer or renderer option"

-------------------------------------------------------------------------------

newtype UnicodeTerminal = UnicodeTerminal (Handle -> Maybe Path -> IO ())

instance RenderSpecial UnicodeTerminal where
        renderSpecial sym = UnicodeTerminal $ \ h _ -> hPutStr h [ch]
                where (Unicode ch) = renderSpecial sym

instance Monoid UnicodeTerminal where
        mempty = UnicodeTerminal $ \ h _ -> return ()
        mappend (UnicodeTerminal f1) (UnicodeTerminal f2) = UnicodeTerminal $ \ h p -> f1 h p >> f2 h p

finalRenders :: [(String,Handle -> PrettyOptions -> DocH -> IO ())]
finalRenders =
        [ ("unicode-terminal", unicodeConsole)
        ] ++ coreRenders

unicodeConsole :: Handle -> PrettyOptions -> DocH -> IO ()
unicodeConsole h w doc = do
    let (UnicodeTerminal pretty) = renderCode w doc
    pretty h Nothing


instance RenderCode UnicodeTerminal where
        rPutStr txt  = UnicodeTerminal $ \ h _ -> hPutStr h txt

        rDoHighlight _ [] = UnicodeTerminal $ \ h _ -> do
                hSetSGR h [Reset]
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

getNavCmd :: IO (Maybe String)
getNavCmd = do
        b_in <- hGetBuffering stdin
        hSetBuffering stdin NoBuffering
        b_out <- hGetBuffering stdin
        hSetBuffering stdout NoBuffering
        ec_in <- hGetEcho stdin
        hSetEcho stdin False
        putStr ("(navigation mode; use arrow keys, escape to quit, '?' for help)")
        res <- readCh []
        putStr ("\n")
        hSetBuffering stdin b_in
        hSetBuffering stdout b_out
        hSetEcho stdin ec_in
        return res
  where
   readCh xs = do
        x <- getChar
        let str = xs ++ [x]
        (case lookup str cmds of
          Just f -> f
          Nothing -> reset) str

   reset str = do
        putStr "\BEL"
        readCh []

   result str _ = return (Just str)

   cmds = [ ("\ESC"  , \ str ->
                       do b <- hReady stdin
                          if b then readCh str
                               else result ":command-line" str)
          , ("\ESC[" , readCh)
          , ("\ESC[A", result "up")
          , ("\ESC[B", result "down")
          , ("\ESC[C", result "right")
          , ("\ESC[D", result "left")
          , ("?",      result ":nav-commands")
          ] ++
          [ (show n, result (show n)) | n <- [0..9] :: [Int] ]




