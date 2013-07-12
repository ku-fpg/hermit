{-# LANGUAGE FlexibleInstances, FlexibleContexts, ScopedTypeVariables, GADTs, TypeFamilies, DeriveDataTypeable #-}

module Language.HERMIT.Shell.Externals where

import qualified GhcPlugins as GHC

import Control.Concurrent.STM
import Control.Monad.State
import Control.Monad.Error

import Data.Monoid
import Data.List (intercalate)
import Data.Dynamic
import qualified Data.Map as M

import Language.HERMIT.Context
import Language.HERMIT.Kure
import Language.HERMIT.Dictionary
import Language.HERMIT.External
import Language.HERMIT.Interp
import Language.HERMIT.Kernel.Scoped
import Language.HERMIT.Parser
import Language.HERMIT.PrettyPrinter.Common

import System.Console.ANSI
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
   SessionStateEffect    :: (CommandLineState -> SessionState -> IO SessionState) -> ShellEffect
   deriving Typeable

data QueryFun :: * where
   QueryString   :: (Injection GHC.ModGuts g, Walker HermitC g) => TranslateH g String                             -> QueryFun
   QueryDocH     ::                                     (PrettyC -> PrettyH CoreTC -> TranslateH CoreTC DocH)      -> QueryFun
   -- These two be can generalized into
   --  (CommandLineState -> IO String)
   Display       ::                                                                                                   QueryFun
   Message       ::                                                String                                          -> QueryFun
   Inquiry       ::                                                (CommandLineState -> SessionState -> IO String) -> QueryFun
   deriving Typeable

instance Extern QueryFun where
   type Box QueryFun = QueryFun
   box i = i
   unbox i = i

data MetaCommand
   = Resume
   | Abort
   | Dump String String String Int
   | LoadFile FilePath  -- load a file on top of the current node
   | SaveFile FilePath
   | ImportR FilePath ExternalName
   | Delete SAST
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
  [ interp $ \ (ShellCommandBox cmd)         -> cmd
  , interp $ \ (RewriteCoreBox rr)           -> AstEffect (Apply rr)
  , interp $ \ (RewriteCoreTCBox rr)         -> AstEffect (Apply rr)
  , interp $ \ (BiRewriteCoreBox br)         -> AstEffect (Apply $ forewardT br)
  , interp $ \ (CrumbBox cr)                 -> AstEffect (Pathfinder (return (mempty @@ cr) :: TranslateH CoreTC LocalPathH))
  , interp $ \ (PathBox p)                   -> AstEffect (Pathfinder (return p :: TranslateH CoreTC LocalPathH))
  , interp $ \ (TranslateCorePathBox tt)     -> AstEffect (Pathfinder tt)
  , interp $ \ (StringBox str)               -> QueryFun (Message str)
  , interp $ \ (TranslateCoreStringBox tt)   -> QueryFun (QueryString tt)
  , interp $ \ (TranslateCoreTCStringBox tt) -> QueryFun (QueryString tt)
  , interp $ \ (TranslateCoreTCDocHBox tt)   -> QueryFun (QueryDocH $ unTranslateDocH tt)
  , interp $ \ (TranslateCoreCheckBox tt)    -> AstEffect (CorrectnessCritera tt)
  , interp $ \ (effect :: AstEffect)         -> AstEffect effect
  , interp $ \ (effect :: ShellEffect)       -> ShellEffect effect
  , interp $ \ (query :: QueryFun)           -> QueryFun query
  , interp $ \ (meta :: MetaCommand)         -> MetaCommand meta
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
   , external "gc"              (Delete . SAST)
       [ "garbage-collect a given AST; does not remove from command log" ]
   , external "gc"              (SessionStateEffect gc)
       [ "garbage-collect all ASTs except for the initial and current AST" ]
   , external "display"         Display
       [ "redisplays current state" ]
   , external "left"            (Direction L)
       [ "move to the next child"]
   , external "right"           (Direction R)
       [ "move to the previous child"]
   , external "up"              (Direction U)
       [ "move to the parent node"]
   , external "down"            (deprecatedIntToPathT 0 :: TranslateH Core LocalPathH) -- TODO: short-term solution
       [ "move to the first child"]
   , external "tag"             Tag
       [ "tag <label> names the current AST with a label" ]
   , external "navigate"        (SessionStateEffect $ \ _ st -> return $ st { cl_nav = True })
       [ "switch to navigate mode" ]
   , external "command-line"    (SessionStateEffect $ \ _ st -> return $ st { cl_nav = False })
       [ "switch to command line mode" ]
   , external "top"             (Direction T)
       [ "move to root of current scope" ]
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
   , external "set-fail-hard" (\ bStr -> SessionStateEffect $ \ _ st ->
        case reads bStr of
            [(b,"")] -> return $ st { cl_failhard = b }
            _        -> return st )
       [ "set-fail-hard <True|False>; False by default"
       , "any rewrite failure causes compilation to abort" ]
   , external "set-auto-corelint" (\ bStr -> SessionStateEffect $ \ _ st ->
        case reads bStr of
            [(b,"")] -> return $ st { cl_corelint = b }
            _        -> return st )
       [ "set-auto-corelint <True|False>; False by default"
       , "run core lint type-checker after every rewrite, reverting on failure" ]
   , external "set-pp"           (\ pp -> SessionStateEffect $ \ _ st ->
       case M.lookup pp pp_dictionary of
         Nothing -> do
            putStrLn $ "List of Pretty Printers: " ++ intercalate ", " (M.keys pp_dictionary)
            return st
         Just _ -> return $ st { cl_pretty = pp })
       [ "set the pretty printer"
       , "use 'set-pp ls' to list available pretty printers" ]
   , external "set-pp-renderer"    changeRenderer
       [ "set the output renderer mode"]
   , external "set-pp-renderer"    showRenderers
       [ "set the output renderer mode"]
   , external "dump"    Dump
       [ "dump <filename> <pretty-printer> <renderer> <width>"]
   , external "set-pp-width" (\ w -> SessionStateEffect $ \ _ st ->
        return $ st { cl_pretty_opts = updateWidthOption w (cl_pretty_opts st) })
       ["set the width of the screen"]
   , external "set-pp-type" (\ str -> SessionStateEffect $ \ _ st ->
        case reads str :: [(ShowOption,String)] of
            [(opt,"")] -> return $ st { cl_pretty_opts = updateTypeShowOption opt (cl_pretty_opts st) }
            _          -> return st)
       ["set how to show expression-level types (Show|Abstact|Omit)"]
   , external "set-pp-coercion" (\ str -> SessionStateEffect $ \ _ st ->
        case reads str :: [(ShowOption,String)] of
            [(opt,"")] -> return $ st { cl_pretty_opts = updateCoShowOption opt (cl_pretty_opts st) }
            _          -> return st)
       ["set how to show coercions (Show|Abstact|Omit)"]
   , external "{"   BeginScope
       ["push current lens onto a stack"]       -- tag as internal
   , external "}"   EndScope
       ["pop a lens off a stack"]               -- tag as internal
   , external "load"  LoadFile
       ["load <filename> : load a file of commands into the current derivation."]
   , external "save"  SaveFile
       ["save <filename> : save the current complete derivation into a file."]
   , external "import-rewrite" ImportR
       ["import-rewrite <filepath> <name-for-rewrite> : create a new rewrite from a file containing a HERMIT script."
       ,"Note that there are significant limitations on the commands the script may contain."] .+ Experiment .+ TODO
   ]

showRenderers :: QueryFun
showRenderers = Message $ "set-renderer " ++ show (map fst finalRenders)

changeRenderer :: String -> ShellEffect
changeRenderer renderer = SessionStateEffect $ \ _ st ->
        case lookup renderer finalRenders of
          Nothing -> return st          -- TODO: should fail with message
          Just r  -> return $ st { cl_render = r }

gc :: CommandLineState -> SessionState -> IO SessionState
gc clst st = do
    let k = cl_kernel clst
        cursor = cl_cursor st
        initSAST = cl_initSAST clst
    asts <- listS k
    mapM_ (deleteS k) [ sast | sast <- asts, sast `notElem` [cursor, initSAST] ]
    return st

----------------------------------------------------------------------------------

type CLM m a = ErrorT String (StateT CommandLineState m) a

-- TODO: Come up with names for these, and/or better characterise these abstractions.
iokm2clm' :: MonadIO m => String -> (a -> CLM m b) -> IO (KureM a) -> CLM m b
iokm2clm' msg ret m = liftIO m >>= runKureM ret (throwError . (msg ++))

iokm2clm :: MonadIO m => String -> IO (KureM a) -> CLM m a
iokm2clm msg = iokm2clm' msg return

iokm2clm'' :: MonadIO m => IO (KureM a) -> CLM m a
iokm2clm'' = iokm2clm ""

data CommandLineState = CommandLineState
        { cl_graph       :: [(SAST,ExprH,SAST)]
        , cl_tags        :: [(String,SAST)]
        -- these three should be in a reader
        , cl_dict        :: Dictionary
        , cl_kernel      :: ScopedKernel
        , cl_initSAST    :: SAST
        -- and the session state (perhaps in a seperate state?)
        , cl_session     :: SessionState
        }

newSAST :: ExprH -> SAST -> CommandLineState -> CommandLineState
newSAST expr sast st = st { cl_session = (cl_session st) { cl_cursor = sast }
                          , cl_graph = (cl_cursor (cl_session st), expr, sast) : cl_graph st
                          }

-- Session-local issues; things that are never saved.
data SessionState = SessionState
        { cl_cursor      :: SAST                                     -- ^ the current AST
        , cl_pretty      :: String                                   -- ^ which pretty printer to use
        , cl_pretty_opts :: PrettyOptions                            -- ^ The options for the pretty printer
        , cl_render      :: Handle -> PrettyOptions -> DocH -> IO () -- ^ the way of outputing to the screen
        , cl_nav         :: Bool                                     -- ^ keyboard input the the nav panel
        , cl_loading     :: Bool                                     -- ^ if loading a file
        , cl_tick        :: TVar (M.Map String Int)                  -- ^ The list of ticked messages
        , cl_corelint    :: Bool                                     -- ^ if true, run core lint on module after each rewrite
        , cl_failhard    :: Bool                                     -- ^ if true, abort on *any* failure
        }

-------------------------------------------------------------------------------

newtype UnicodeTerminal = UnicodeTerminal (Handle -> Maybe PathH -> IO ())

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
unicodeConsole h opts doc = do
    let (UnicodeTerminal prty) = renderCode opts doc
    prty h Nothing

instance RenderCode UnicodeTerminal where
        rPutStr txt  = UnicodeTerminal $ \ h _ -> hPutStr h txt

        rDoHighlight _ [] = UnicodeTerminal $ \ h _ -> hSetSGR h [Reset]
        rDoHighlight _ (Color col:_) = UnicodeTerminal $ \ h _ -> do
                hSetSGR h [ Reset ]
                hSetSGR h $ case col of
                        KeywordColor  -> [ SetConsoleIntensity BoldIntensity
                                         , SetColor Foreground Dull Blue
                                         ]
                        SyntaxColor   -> [ SetColor Foreground Dull Red ]
                        IdColor       -> []   -- as is
                        CoercionColor -> [ SetColor Foreground Dull Yellow ]
                        TypeColor     -> [ SetColor Foreground Dull Green ]
                        LitColor      -> [ SetColor Foreground Dull Cyan ]
                        WarningColor  -> [ SetSwapForegroundBackground True, SetColor Foreground Vivid Yellow ]
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
              else fail $ "Cannot find AST #" ++ show n ++ "."
      GotoTag tag -> case lookup tag (cl_tags st) of
                       Just sast -> return $ sess_st { cl_cursor = sast }
                       Nothing   -> fail $ "Cannot find tag " ++ show tag ++ "."
      Step -> do
           let ns = [ edge | edge@(s,_,_) <- cl_graph st, s == cl_cursor (cl_session st) ]
           case ns of
             [] -> fail "Cannot step forward (no more steps)."
             [(_,cmd,d) ] -> do
                           putStrLn $ "step : " ++ unparseExprH cmd
                           return $ sess_st { cl_cursor = d }
             _ -> fail "Cannot step forward (multiple choices)"
      Back -> do
           let ns = [ edge | edge@(_,_,d) <- cl_graph st, d == cl_cursor (cl_session st) ]
           case ns of
             []         -> fail "Cannot step backwards (no more steps)."
             [(s,cmd,_) ] -> do
                           putStrLn $ "back, unstepping : " ++ unparseExprH cmd
                           return $ sess_st { cl_cursor = s }
             _          -> fail "Cannot step backwards (multiple choices, impossible!)."

-------------------------------------------------------------------------------

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

-------------------------------------------------------------------------------
