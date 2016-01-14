{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

module HERMIT.Shell.Externals where

import Control.Arrow
import Control.Monad (liftM)
import Control.Monad.Reader (asks)
import Control.Monad.State (gets, modify)

import Data.Dynamic (fromDynamic)
import Data.List (intercalate)
import qualified Data.Map as M
import Data.Maybe (fromMaybe)

import HERMIT.External
import HERMIT.Kernel
import HERMIT.Kure
import HERMIT.Lemma
import HERMIT.Parser
import HERMIT.Plugin.Renderer
import HERMIT.Plugin.Types
import HERMIT.PrettyPrinter.Common

import HERMIT.Dictionary.Reasoning

import HERMIT.Shell.Dictionary
import HERMIT.Shell.KernelEffect
import HERMIT.Shell.Proof as Proof
import HERMIT.Shell.ScriptToRewrite
import HERMIT.Shell.ShellEffect
import HERMIT.Shell.Types

----------------------------------------------------------------------------------

shell_externals :: [External]
shell_externals = map (.+ Shell)
    [ external "resume"          Resume    -- HERMIT Kernel Exit
        [ "stops HERMIT; resumes compile" ]
    , external "abort"           Abort     -- UNIX Exit
        [ "hard UNIX-style exit; does not return to GHC; does not save" ]
    , external "continue"        Continue  -- Shell Exit, but not HERMIT
        [ "exits shell; resumes HERMIT" ]
    , external "gc"              Delete
        [ "garbage-collect a given AST" ]
    , external "gc"              (CLSModify gc)
        [ "garbage-collect all ASTs except for the initial and current AST" ]
    , external "display"         (CLSModify $ printWindowAlways Nothing)
        [ "redisplays current state" ]
    , external "up"              (Direction U)
        [ "move to the parent node"]
    , external "navigate"        (CLSModify $ modify $ \ st -> st { cl_nav = True })
        [ "switch to navigate mode" ]
    , external "command-line"    (CLSModify $ modify $ \ st -> st { cl_nav = False })
        [ "switch to command line mode" ]
    , external "set-window"      (CLSModify $ setWindow >> printWindow Nothing)
        [ "fix the window to the current focus" ]
    , external "top"             (Direction T)
        [ "move to root of current scope" ]
    , external "log"             (Inquiry showDerivationTree)
        [ "go back in the derivation" ]                                          .+ VersionControl
    , external "back"            (CLSModify $ versionCmd Back)
        [ "go back in the derivation" ]                                          .+ VersionControl
    , external "step"            (CLSModify $ versionCmd Step)
        [ "step forward in the derivation" ]                                     .+ VersionControl
    , external "goto"            (CLSModify . versionCmd . Goto)
        [ "goto a specific step in the derivation" ]                             .+ VersionControl
    , external "goto"            (CLSModify . versionCmd . GotoTag)
        [ "goto a specific step in the derivation by tag name" ]                 .+ VersionControl
    , external "tag"             (CLSModify . versionCmd . Tag)
        [ "name the current step in the derivation" ]                            .+ VersionControl
    , external "diff"            Diff
        [ "show diff of two ASTs" ]                                              .+ VersionControl
    , external "set-pp-diffonly" (\ bStr -> CLSModify $
        case reads bStr of
            [(b,"")] -> modify (\st -> st { cl_diffonly = b }) >> printWindow Nothing
            _        -> fail "valid arguments are True and False" )
        [ "set-pp-diffonly <True|False>; False by default"
        , "print diffs rather than full code after a rewrite" ]
    , external "set-fail-hard"   (\ bStr -> CLSModify $
        case reads bStr of
            [(b,"")] -> modify $ \ st -> st { cl_failhard = b }
            _        -> fail "valid arguments are True and False" )
        [ "set-fail-hard <True|False>; False by default"
        , "any rewrite failure causes compilation to abort" ]
    , external "set-auto-corelint" (\ bStr -> CLSModify $
        case reads bStr of
            [(b,"")] -> modify $ flip setCoreLint b
            _        -> fail "valid arguments are True and False" )
        [ "set-auto-corelint <True|False>; False by default"
        , "run core lint type-checker after every rewrite, reverting on failure" ]
    , external "set-pp"          (\ name -> CLSModify $
        case M.lookup name pp_dictionary of
            Nothing -> fail $ "List of Pretty Printers: " ++ intercalate ", " (M.keys pp_dictionary)
            Just pp -> do modify $ \ st -> setPrettyOpts (setPretty st pp) (cl_pretty_opts st) -- careful to preserve the current options
                          printWindow Nothing)
        [ "set the pretty printer"
        , "use 'set-pp ls' to list available pretty printers" ]
    , external "set-pp-renderer"    (PluginComp . changeRenderer)
        [ "set the output renderer mode"]
    , external "set-pp-renderer"    showRenderers
        [ "set the output renderer mode"]
    , -- DEPRECATED - this dump behavior uses the current pretty printer selected in the shell
      external "dump" (\pp fp r w -> CLSModify (dump fp pp r w))
        [ "dump <filename> <renderer> <width> - DEPRECATED"]
    , external "dump" (\fp pp r w -> CLSModify (dump fp pp r w))
        [ "dump <filename> <pretty-printer> <renderer> <width>"]
    , external "dump-lemma" ((\nm fp pp r w -> getLemmaByNameT nm >>> liftPrettyH (pOptions pp) (ppLemmaT pp nm) >>> dumpT fp pp r w) :: LemmaName -> FilePath -> PrettyPrinter -> String -> Int -> TransformH LCoreTC ())
        [ "Dump named lemma to a file."
        , "dump-lemma <lemma-name> <filename> <pretty-printer> <renderer> <width>" ]
    , external "dump-lemma" ((\pp nm fp r w -> getLemmaByNameT nm >>> liftPrettyH (pOptions pp) (ppLemmaT pp nm) >>> dumpT fp pp r w) :: PrettyPrinter -> LemmaName -> FilePath -> String -> Int -> TransformH LCoreTC ())
        [ "Dump named lemma to a file."
        , "dump-lemma <lemma-name> <filename> <pretty-printer> <renderer> <width>" ]
    , external "set-pp-width" (\ w -> CLSModify $ do
            modify $ \ st -> setPrettyOpts st (updateWidthOption w (cl_pretty_opts st))
            printWindow Nothing)
        ["set the width of the screen"]
    , external "set-pp-type" (\ str -> CLSModify $
        case reads str :: [(ShowOption,String)] of
            [(opt,"")] -> do modify $ \ st -> setPrettyOpts st (updateTypeShowOption opt (cl_pretty_opts st))
                             printWindow Nothing
            _          -> fail "valid arguments are Show, Abstract, and Omit")
        ["set how to show expression-level types (Show|Abstact|Omit)"]
    , external "set-pp-coercion" (\ str -> CLSModify $
        case reads str :: [(ShowOption,String)] of
            [(opt,"")] -> do modify $ \ st -> setPrettyOpts st (updateCoShowOption opt (cl_pretty_opts st))
                             printWindow Nothing
            _          -> fail "valid arguments are Show, Abstract, and Omit")
        ["set how to show coercions (Show|Abstact|Omit)"]
    , external "set-pp-uniques" (\ str -> CLSModify $
        case reads str of
            [(b,"")] -> do modify $ \ st -> setPrettyOpts st ((cl_pretty_opts st) { po_showUniques = b })
                           printWindow Nothing
            _        -> fail "valid arguments are True and False")
        ["set whether uniques are printed with variable names"]
    , external "{"   BeginScope
        ["push current lens onto a stack"]       -- tag as internal
    , external "}"   EndScope
        ["pop a lens off a stack"]               -- tag as internal
    , external "load"  LoadFile
        ["load <script-name> <file-name> : load a HERMIT script from a file and save it under the specified name."]
    , external "load-and-run"  loadAndRun
        ["load-and-run <file-name> : load a HERMIT script from a file and run it immediately."]
    , external "save"  (SaveFile False)
        ["save <filename> : save the current complete derivation into a file."]
    , external "save-verbose"  (SaveFile True)
        ["save-verbose <filename> : save the current complete derivation into a file,"
        ,"including output of each command as a comment."]
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
    , external "stop-script" (CLSModify $ setRunningScript Nothing)
        [ "Stop running the current script." ]
    --, external "test-rewrites" (testRewrites :: [(ExternalName,RewriteH Core)] -> TransformH Core String)
    --  ["Test a given set of rewrites to see if they succeed"] .+ Experiment
    , external "possible-rewrites" (testAllT:: CommandLineState -> TransformH LCore String)
        ["Test all given set of rewrites to see if they succeed"] .+ Experiment
    -- TODO: maybe add a "list-scripts" as well that just lists the names of loaded scripts?
    ] ++ Proof.externals

gc :: CLT IO ()
gc = do
    k <- asks pr_kernel
    cursor <- gets cl_cursor
    asts <- listK k
    mapM_ (deleteK k) [ ast | (ast,_,_) <- asts, ast `notElem` [cursor, firstAST] ]

----------------------------------------------------------------------------------

setWindow :: CLT IO ()
setWindow = modify $ \ st ->
    let ps = fromMaybe ([],mempty) (M.lookup (cl_cursor st) (cl_foci st))
    in st { cl_window = pathStack2Path ps }

showRenderers :: QueryFun ()
showRenderers = message $ "set-renderer " ++ show (map fst shellRenderers)

--------------------------------------------------------

versionCmd :: VersionCmd -> CLT IO ()
versionCmd whereTo = do
    k <- asks pr_kernel
    all_asts <- listK k
    case whereTo of
        Goto ast ->
            if ast `elem` [ ast' | (ast',_,_) <- all_asts ]
                then modify (setCursor ast) >> printWindow Nothing
                else fail $ "Cannot find AST #" ++ show ast ++ "."
        GotoTag nm -> do
            tags <- gets cl_tags
            case [ ast | (ast,nms) <- M.toList tags, nm `elem` nms ] of
                [] -> fail $ "No tag named: " ++ nm
                (ast:_) -> modify (setCursor ast) >> printWindow Nothing
        Tag nm -> do
            modify $ \st -> st { cl_tags = M.insertWith (++) (cl_cursor st) [nm] (cl_tags st) }
            cl_putStrLn $ "Tag: " ++ nm ++ " added."
        Step -> do
            cursor <- gets cl_cursor
            let ns = [ (fromMaybe "unknown" msg, ast) | (ast,msg,Just p) <- all_asts, p == cursor ]
            case ns of
                [] -> fail "Cannot step forward (no more steps)."
                [(cmd,ast)] -> do
                    cl_putStrLn $ "step : " ++ cmd
                    modify $ setCursor ast
                    printWindow Nothing
                _ -> fail $ "Cannot step forward (multiple choices), use goto {"
                                ++ intercalate "," (map (show.snd) ns) ++ "}"
        Back -> do
            cursor <- gets cl_cursor
            let ns = [ (fromMaybe "unknown" msg, p) | (ast,msg,Just p) <- all_asts, ast == cursor ]
            case ns of
                [] -> fail "Cannot step backwards (no more steps)."
                [(cmd,ast)] -> do
                    cl_putStrLn $ "back, unstepping : " ++ cmd
                    modify $ setCursor ast
                    printWindow Nothing
                _ -> fail "Cannot step backwards (multiple choices, impossible!)."

-------------------------------------------------------------------------------

showDerivationTree :: PluginReader -> CommandLineState -> IO String
showDerivationTree r s = do
    let k = pr_kernel r
        cursor = cl_cursor s
    all_asts <- listK k
    let graph = [ (a,[fromMaybe "-- command missing!" b],c) | (c,b,Just a) <- all_asts ]
    return $ unlines $ showRefactorTrail graph firstAST cursor

showRefactorTrail :: (Eq a, Show a) => [(a,[String],a)] -> a -> a -> [String]
showRefactorTrail db a me =
        case [ (b,c) | (a0,b,c) <- db, a == a0 ] of
           [] -> [show' 3 a ++ " " ++ dot]
           ((b,c):bs) ->
                      [show' 3 a ++ " " ++ dot ++ (if not (null bs) then "->" else "") ] ++
                      ["    " ++ "| " ++ txt | txt <- b ] ++
                      showRefactorTrail db c me ++
                      if null bs
                      then []
                      else [] :
                          showRefactorTrail [ (a',b',c') | (a',b',c') <- db
                                                         , not (a == a' && c == c')
                                                         ] a me

  where dot = if a == me then "*" else "o"
        show' n x = replicate (n - length (show a)) ' ' ++ show x

-------------------------------------------------------------------------------

displayScripts :: QueryFun ()
displayScripts = Inquiry (const (return . showScripts . cl_scripts))

showScripts :: [(ScriptName,Script)] -> String
showScripts = concatMap (\ (name,script) -> name ++ ": " ++ unparseScript script ++ "\n\n")

-------------------------------------------------------------------------------
testAllT :: CommandLineState -> TransformH LCore String
testAllT st = do
                let es  = cl_externals st
                    mbs = map (\d -> (externName d, fromDynamic (externDyn d) :: Maybe RewriteLCoreBox)) es
                    namedRewrites = [(name ,unbox boxedR) | (name, Just boxedR) <- mbs]
                testRewrites False namedRewrites

testRewrites :: Bool-> [(ExternalName, RewriteH LCore)] -> TransformH LCore String
testRewrites debug rewrites = case debug of
                       True -> let list =  mapM (\ (n,r) -> liftM (f n) (testM r)) rewrites
                               in  liftM unlines list
                       False -> let list = mapM (\ (n,r) -> liftM (g n) (testM r)) rewrites
                                    filtered = liftM (filter(\x -> snd x)) list
                                    res = liftM (map (\ (n,b) -> f n b )) filtered
                                in liftM unlines res
{-testRewrites rewrites = let list =  mapM (\ (n,r) -> liftM (g n) (testM r)) rewrites
                            filtered = liftM (filter (\ x -> snd x))  list
                            res =  liftM (map (\ (n, b) -> f n b)) filtered
                        in  liftM unlines res
-}
  where
   f :: ExternalName -> Bool -> String
   f x True  = x++" would succeed."
   f x False = x++" would fail."
   g x y  = (x,y)
