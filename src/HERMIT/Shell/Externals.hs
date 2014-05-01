{-# LANGUAGE FlexibleContexts, ScopedTypeVariables #-}

module HERMIT.Shell.Externals where

import Control.Applicative

import Data.Monoid
import Data.List (intercalate)
import qualified Data.Map as M

import HERMIT.Context
import HERMIT.Kure
import HERMIT.External
import HERMIT.Kernel.Scoped
import HERMIT.Parser
import HERMIT.Plugin.Renderer
import HERMIT.PrettyPrinter.Common

import HERMIT.Shell.Dictionary
import HERMIT.Shell.Interpreter
import HERMIT.Shell.KernelEffect
import HERMIT.Shell.Proof as Proof
import HERMIT.Shell.ScriptToRewrite
import HERMIT.Shell.ShellEffect
import HERMIT.Shell.Types

----------------------------------------------------------------------------------

-- | There are five types of commands.
data ShellCommand = KernelEffect KernelEffect -- ^ Command that modifies the state of the (scoped) kernel.
                  | ScriptEffect ScriptEffect -- ^ Command that deals with script files.
                  | ShellEffect  ShellEffect  -- ^ Command that modifies the state of the shell.
                  | QueryFun     QueryFun     -- ^ Command that queries the AST with a Transform (read only).
                  | ProofCommand ProofCommand -- ^ Command that deals with proofs.

-- | Interpret a boxed thing as one of the four possible shell command types.
interpShellCommand :: [Interp ShellCommand]
interpShellCommand =
  [ interp $ \ (RewriteCoreBox rr)           -> KernelEffect (Apply rr)
  , interp $ \ (RewriteCoreTCBox rr)         -> KernelEffect (Apply rr)
  , interp $ \ (BiRewriteCoreBox br)         -> KernelEffect (Apply $ whicheverR br)
  , interp $ \ (CrumbBox cr)                 -> KernelEffect (Pathfinder (return (mempty @@ cr) :: TransformH CoreTC LocalPathH))
  , interp $ \ (PathBox p)                   -> KernelEffect (Pathfinder (return p :: TransformH CoreTC LocalPathH))
  , interp $ \ (TransformCorePathBox tt)     -> KernelEffect (Pathfinder tt)
  , interp $ \ (TransformCoreTCPathBox tt)   -> KernelEffect (Pathfinder tt)
  , interp $ \ (StringBox str)               -> QueryFun (message str)
  , interp $ \ (TransformCoreStringBox tt)   -> QueryFun (QueryString tt)
  , interp $ \ (TransformCoreTCStringBox tt) -> QueryFun (QueryString tt)
  , interp $ \ (TransformCoreTCDocHBox tt)   -> QueryFun (QueryDocH $ unTransformDocH tt)
  , interp $ \ (TransformCoreCheckBox tt)    -> QueryFun (CorrectnessCritera tt)
  , interp $ \ (TransformCoreTCCheckBox tt)  -> QueryFun (CorrectnessCritera tt)
  , interp $ \ (effect :: KernelEffect)      -> KernelEffect effect
  , interp $ \ (effect :: ShellEffect)       -> ShellEffect effect
  , interp $ \ (effect :: ScriptEffect)      -> ScriptEffect effect
  , interp $ \ (query :: QueryFun)           -> QueryFun query
  , interp $ \ (cmd :: ProofCommand)         -> ProofCommand cmd
  ]

shell_externals :: [External]
shell_externals = map (.+ Shell)
   [
     external "resume"          Resume    -- HERMIT Kernel Exit
       [ "stops HERMIT; resumes compile" ]
   , external "abort"           Abort     -- UNIX Exit
       [ "hard UNIX-style exit; does not return to GHC; does not save" ]
   , external "continue"        Continue  -- Shell Exit, but not HERMIT
       [ "exits shell; resumes HERMIT" ]
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
   , external "down"            (deprecatedIntToPathT 0 :: TransformH Core LocalPathH) -- TODO: short-term solution
       [ "move to the first child"]
   , external "navigate"        (CLSModify $ \ st -> return $ st { cl_nav = True })
       [ "switch to navigate mode" ]
   , external "command-line"    (CLSModify $ \ st -> return $ st { cl_nav = False })
       [ "switch to command line mode" ]
   , external "set-window"      (CLSModify setWindow)
       [ "fix the window to the current focus" ]
   , external "top"             (Direction T)
       [ "move to root of current scope" ]
   , external "back"            (CLSModify $ versionCmd Back)
       [ "go back in the derivation" ]                                          .+ VersionControl
   , external "log"             (Inquiry showDerivationTree)
       [ "go back in the derivation" ]                                          .+ VersionControl
   , external "step"            (CLSModify $ versionCmd Step)
       [ "step forward in the derivation" ]                                     .+ VersionControl
   , external "goto"            (CLSModify . versionCmd . Goto)
       [ "goto a specific step in the derivation" ]                             .+ VersionControl
   , external "goto"            (CLSModify . versionCmd . GotoTag)
       [ "goto a named step in the derivation" ]
   , external "tag"             (CLSModify . versionCmd . AddTag)
       [ "tag <label> names the current AST with a label" ]                     .+ VersionControl
   , external "diff"            (\ s1 s2 -> Diff (SAST s1) (SAST s2))
       [ "show diff of two ASTs" ]                                              .+ VersionControl
   , external "set-pp-diffonly" (\ bStr -> CLSModify $ \ st ->
        case reads bStr of
            [(b,"")] -> return $ setDiffOnly st b
            _        -> return st)
       [ "set-pp-diffonly <True|False>; False by default"
       , "print diffs rather than full code after a rewrite" ]
   , external "set-fail-hard"   (\ bStr -> CLSModify $ \ st ->
        case reads bStr of
            [(b,"")] -> return $ setFailHard st b
            _        -> return st)
       [ "set-fail-hard <True|False>; False by default"
       , "any rewrite failure causes compilation to abort" ]
   , external "set-auto-corelint" (\ bStr -> CLSModify $ \ st ->
        case reads bStr of
            [(b,"")] -> return $ setCoreLint st b
            _        -> return st )
       [ "set-auto-corelint <True|False>; False by default"
       , "run core lint type-checker after every rewrite, reverting on failure" ]
   , external "set-pp"          (\ name -> CLSModify $ \ st ->
       case M.lookup name pp_dictionary of
         Nothing -> do
            putStrLn $ "List of Pretty Printers: " ++ intercalate ", " (M.keys pp_dictionary)
            return st
         Just pp -> return $ setPretty st pp)
       [ "set the pretty printer"
       , "use 'set-pp ls' to list available pretty printers" ]
   , external "set-pp-renderer"    (PluginComp . changeRenderer)
       [ "set the output renderer mode"]
   , external "set-pp-renderer"    showRenderers
       [ "set the output renderer mode"]
   , external "dump" (Dump (\st -> liftPrettyH (cl_pretty_opts st) $ pCoreTC $ cl_pretty st))
       [ "dump <filename> <renderer> <width>"]
   , external "set-pp-width" (\ w -> CLSModify $ \ st ->
        return $ setPrettyOpts st (updateWidthOption w (cl_pretty_opts st)))
       ["set the width of the screen"]
   , external "set-pp-type" (\ str -> CLSModify $ \ st ->
        case reads str :: [(ShowOption,String)] of
            [(opt,"")] -> return $ setPrettyOpts st (updateTypeShowOption opt (cl_pretty_opts st))
            _          -> return st)
       ["set how to show expression-level types (Show|Abstact|Omit)"]
   , external "set-pp-coercion" (\ str -> CLSModify $ \ st ->
        case reads str :: [(ShowOption,String)] of
            [(opt,"")] -> return $ setPrettyOpts st (updateCoShowOption opt (cl_pretty_opts st))
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
   , external "load-as-rewrite" (\ rewriteName fileName -> SeqMeta [LoadFile rewriteName fileName, ScriptToRewrite rewriteName rewriteName])
       ["load-as-rewrite <rewrite-name> <filepath> : load a HERMIT script from a file, and convert it to a rewrite."
       ,"Note that there are significant limitations on the commands the script may contain."] .+ Experiment .+ TODO
   , external "script-to-rewrite" ScriptToRewrite
       ["script-to-rewrite <rewrite-name> <script-name> : create a new rewrite from a pre-loaded (or manually defined) HERMIT script."
       ,"Note that there are significant limitations on the commands the script may contain."] .+ Experiment .+ TODO
   , external "define-script" DefineScript
       ["Define a new HERMIT script and bind it to a name."
       ,"Note that any names in the script will not be resolved until the script is *run*."
       ,"Example usage: define-script \"MyScriptName\" \"any-td beta-reduce ; let-subst ; bash\""]
   , external "define-rewrite" (\ name str -> SeqMeta [DefineScript name str, ScriptToRewrite name name])
       ["Define a new HERMIT rewrite and bind it to a name."
       ,"Note that this also saves the input script under the same name."
       ,"Example usage: define-rewrite \"MyRewriteName\" \"let-subst >>> bash\""]
   , external "run-script" RunScript
       ["Run a pre-loaded (or manually defined) HERMIT script."
       ,"Note that any names in the script will not be resolved until the script is *run*." ]
   , external "display-scripts" displayScripts
       ["Display all loaded scripts."]
     -- TODO: maybe add a "list-scripts" as well that just lists the names of loaded scripts?
   ] ++ Proof.externals

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
    paths <- concat <$> pathS (cl_kernel st) (cl_cursor st)
    return $ st { cl_window = paths }

showRenderers :: QueryFun
showRenderers = message $ "set-renderer " ++ show (map fst shellRenderers)

--------------------------------------------------------

versionCmd :: VersionCmd -> CommandLineState -> IO CommandLineState
versionCmd whereTo st =
    case whereTo of
        Goto n -> do
            all_nds <- listS (cl_kernel st)
            if SAST n `elem` all_nds
                then return $ setCursor st (SAST n)
                else fail $ "Cannot find AST #" ++ show n ++ "."
        GotoTag tag -> case lookup tag (vs_tags (cl_version st)) of
                        Just sast -> return $ setCursor st sast
                        Nothing   -> fail $ "Cannot find tag " ++ show tag ++ "."
        Step -> do
            let ns = [ edge | edge@(s,_,_) <- vs_graph (cl_version st), s == cl_cursor st ]
            case ns of
                [] -> fail "Cannot step forward (no more steps)."
                [(_,cmd,d) ] -> do
                    putStrLn $ "step : " ++ unparseExprH cmd
                    return $ setCursor st d
                _ -> fail "Cannot step forward (multiple choices)"
        Back -> do
            let ns = [ edge | edge@(_,_,d) <- vs_graph (cl_version st), d == cl_cursor st ]
            case ns of
                []         -> fail "Cannot step backwards (no more steps)."
                [(s,cmd,_) ] -> do
                    putStrLn $ "back, unstepping : " ++ unparseExprH cmd
                    return $ setCursor st s
                _          -> fail "Cannot step backwards (multiple choices, impossible!)."
        AddTag tag -> do
            return $ st { cl_version = (cl_version st) { vs_tags = (tag, cl_cursor st) : vs_tags (cl_version st) }}

-------------------------------------------------------------------------------

showDerivationTree :: CommandLineState -> IO String
showDerivationTree st = return $ unlines $ showRefactorTrail graph tags start me
  where
          graph = [ (a,[unparseExprH b],c) | (SAST a,b,SAST c) <- vs_graph (cl_version st) ]
          tags  = [ (n,nm) | (nm,SAST n) <- vs_tags (cl_version st) ]
          SAST me = cl_cursor st
          SAST start = cl_initSAST st

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


-------------------------------------------------------------------------------

displayScripts :: QueryFun
displayScripts = Inquiry (return . showScripts . cl_scripts)

showScripts :: [(ScriptName,Script)] -> String
showScripts = concatMap (\ (name,script) -> name ++ ": " ++ unparseScript script ++ "\n\n")

-------------------------------------------------------------------------------
