{-# LANGUAGE ScopedTypeVariables #-}

module HERMIT.Shell.Externals where

import Control.Applicative

import Data.Monoid
import Data.List (intercalate)
import qualified Data.Map as M

import HERMIT.Context
import HERMIT.Kure
import HERMIT.Dictionary
import HERMIT.External
import HERMIT.Interp
import HERMIT.Kernel.Scoped
import HERMIT.Parser
import HERMIT.PrettyPrinter.Common

import HERMIT.Shell.Renderer
import HERMIT.Shell.Types

----------------------------------------------------------------------------------

interpShellCommand :: [Interp ShellCommand]
interpShellCommand =
  [ interp $ \ (RewriteCoreBox rr)           -> AstEffect (Apply rr)
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

shell_externals :: [External]
shell_externals = map (.+ Shell)
   [
     external "resume"          Resume    -- HERMIT Kernel Exit
       [ "stops HERMIT; resumes compile" ]
   , external "abort"           Abort     -- UNIX Exit
       [ "hard UNIX-style exit; does not return to GHC; does not save" ]
   , external "gc"              (Delete . SAST)
       [ "garbage-collect a given AST; does not remove from command log" ]
   , external "gc"              (CLSModify gc)
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
   , external "navigate"        (CLSModify $ \ st -> return $ st { cl_nav = True })
       [ "switch to navigate mode" ]
   , external "command-line"    (CLSModify $ \ st -> return $ st { cl_nav = False })
       [ "switch to command line mode" ]
   , external "set-window"      (CLSModify setWindow)
       [ "fix the window to the current focus" ]
   , external "top"             (Direction T)
       [ "move to root of current scope" ]
   , external "back"            (CLSModify $ navigation Back)
       [ "go back in the derivation" ]                                          .+ VersionControl
   , external "log"             (Inquiry showDerivationTree)
       [ "go back in the derivation" ]                                          .+ VersionControl
   , external "step"            (CLSModify $ navigation Step)
       [ "step forward in the derivation" ]                                     .+ VersionControl
   , external "goto"            (CLSModify . navigation . Goto)
       [ "goto a specific step in the derivation" ]                             .+ VersionControl
   , external "goto"            (CLSModify . navigation . GotoTag)
       [ "goto a named step in the derivation" ]
   , external "set-fail-hard" (\ bStr -> CLSModify $ \ st ->
        case reads bStr of
            [(b,"")] -> return $ st { cl_failhard = b }
            _        -> return st )
       [ "set-fail-hard <True|False>; False by default"
       , "any rewrite failure causes compilation to abort" ]
   , external "set-auto-corelint" (\ bStr -> CLSModify $ \ st ->
        case reads bStr of
            [(b,"")] -> return $ st { cl_corelint = b }
            _        -> return st )
       [ "set-auto-corelint <True|False>; False by default"
       , "run core lint type-checker after every rewrite, reverting on failure" ]
   , external "set-pp"           (\ pp -> CLSModify $ \ st ->
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
   , external "set-pp-width" (\ w -> CLSModify $ \ st ->
        return $ st { cl_pretty_opts = updateWidthOption w (cl_pretty_opts st) })
       ["set the width of the screen"]
   , external "set-pp-type" (\ str -> CLSModify $ \ st ->
        case reads str :: [(ShowOption,String)] of
            [(opt,"")] -> return $ st { cl_pretty_opts = updateTypeShowOption opt (cl_pretty_opts st) }
            _          -> return st)
       ["set how to show expression-level types (Show|Abstact|Omit)"]
   , external "set-pp-coercion" (\ str -> CLSModify $ \ st ->
        case reads str :: [(ShowOption,String)] of
            [(opt,"")] -> return $ st { cl_pretty_opts = updateCoShowOption opt (cl_pretty_opts st) }
            _          -> return st)
       ["set how to show coercions (Show|Abstact|Omit)"]
   , external "{"   BeginScope
       ["push current lens onto a stack"]       -- tag as internal
   , external "}"   EndScope
       ["pop a lens off a stack"]               -- tag as internal
   , external "load"  LoadFile
       ["load <script-name> <file-name> : load a HERMIT script from a file and save it under the specified name."]
   , external "load-and-run"  loadAndRun
       ["load-and-run <file-name> : load a HERMIT script from a file and run it immediately."]
   , external "save"  SaveFile
       ["save <filename> : save the current complete derivation into a file."]
   , external "save-script" SaveScript
       ["save-script <filename> <script name> : save a loaded or manually defined script to a file." ]
   , external "load-as-rewrite" (\ rewriteName fileName -> SeqMeta [LoadFile rewriteName fileName, ScriptToRewrite rewriteName])
       ["load-as-rewrite <rewrite-name> <filepath> : load a HERMIT script from a file, and create a rewrite with the same name."
       ,"Note that there are significant limitations on the commands the script may contain."] .+ Experiment .+ TODO
   , external "script-to-rewrite" ScriptToRewrite
       ["script-to-rewrite <script-name> : create a new rewrite from a pre-loaded (or manually defined) HERMIT script."
       ,"Note that there are significant limitations on the commands the script may contain."] .+ Experiment .+ TODO
   , external "define-script" DefineScript
       ["Define a new HERMIT script and bind it to a name."
       ,"Note that any names in the script will not be resolved until the script is *run*."
       ,"Example usage: define-script \"MyScriptName\" \"let-subst >>> bash\""]
   , external "run-script" RunScript
       ["Run a pre-loaded (or manually defined) HERMIT script."
       ,"Note that any names in the script will not be resolved until the script is *run*." ]
   ]

gc :: CommandLineState -> IO CommandLineState
gc st = do
    let k = cl_kernel st
        cursor = cl_cursor st
        initSAST = cl_initSAST st
    asts <- listS k
    mapM_ (deleteS k) [ sast | sast <- asts, sast `notElem` [cursor, initSAST] ]
    return st

----------------------------------------------------------------------------------

setWindow :: CommandLineState -> IO CommandLineState
setWindow st = do
    paths <- runKureM concat fail <$> pathS (cl_kernel st) (cl_cursor st)
    return $ st { cl_window = paths }

--------------------------------------------------------

navigation :: Navigation -> CommandLineState -> IO CommandLineState
navigation whereTo st =
    case whereTo of
      Goto n -> do
           all_nds <- listS (cl_kernel st)
           if SAST n `elem` all_nds
              then return $ st { cl_cursor = SAST n }
              else fail $ "Cannot find AST #" ++ show n ++ "."
      GotoTag tag -> case lookup tag (vs_tags (cl_version st)) of
                       Just sast -> return $ st { cl_cursor = sast }
                       Nothing   -> fail $ "Cannot find tag " ++ show tag ++ "."
      Step -> do
           let ns = [ edge | edge@(s,_,_) <- vs_graph (cl_version st), s == cl_cursor st ]
           case ns of
             [] -> fail "Cannot step forward (no more steps)."
             [(_,cmd,d) ] -> do
                           putStrLn $ "step : " ++ unparseExprH cmd
                           return $ st { cl_cursor = d }
             _ -> fail "Cannot step forward (multiple choices)"
      Back -> do
           let ns = [ edge | edge@(_,_,d) <- vs_graph (cl_version st), d == cl_cursor st ]
           case ns of
             []         -> fail "Cannot step backwards (no more steps)."
             [(s,cmd,_) ] -> do
                           putStrLn $ "back, unstepping : " ++ unparseExprH cmd
                           return $ st { cl_cursor = s }
             _          -> fail "Cannot step backwards (multiple choices, impossible!)."

-------------------------------------------------------------------------------

showDerivationTree :: CommandLineState -> IO String
showDerivationTree st = return $ unlines $ showRefactorTrail graph tags 0 me
  where
          graph = [ (a,[unparseExprH b],c) | (SAST a,b,SAST c) <- vs_graph (cl_version st) ]
          tags  = [ (n,nm) | (nm,SAST n) <- vs_tags (cl_version st) ]
          SAST me = cl_cursor st

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
