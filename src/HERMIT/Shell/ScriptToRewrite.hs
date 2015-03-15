{-# LANGUAGE ConstraintKinds, DeriveDataTypeable, FlexibleContexts, LambdaCase,
             MultiParamTypeClasses, ScopedTypeVariables, TypeFamilies #-}

module HERMIT.Shell.ScriptToRewrite
    ( -- * Converting Scripts to Rewrites
      addScriptToDict
    , loadAndRun
    , lookupScript
    , parseScriptCLT
    , performScriptEffect
    , popScriptLine
    , pushScriptLine
    , pushScript
    , runScript
    , fileToScript
    , scriptToRewrite
    , ScriptEffect(..)
    ) where

import Control.Arrow
import Control.Monad
import Control.Monad.IO.Class (liftIO)
import Control.Monad.State (MonadState, gets, modify)
import Control.Exception hiding (catch)

import Data.Dynamic
import qualified Data.Map as M

import HERMIT.Context(LocalPathH)
import HERMIT.External
import HERMIT.Kernel
import HERMIT.Kure
import HERMIT.Lemma
import HERMIT.Parser(Script, ExprH, unparseExprH, parseScript, unparseScript)
import HERMIT.Dictionary.Reasoning
import HERMIT.PrettyPrinter.Common
import qualified HERMIT.PrettyPrinter.Clean as Clean

import HERMIT.Shell.KernelEffect
import HERMIT.Shell.Interpreter
import HERMIT.Shell.ShellEffect
import HERMIT.Shell.Types

import qualified Text.PrettyPrint.MarkedHughesPJ as PP
------------------------------------

type RewriteName = String

data ScriptEffect
    = DefineScript ScriptName String
    | LoadFile ScriptName FilePath  -- load a file on top of the current node
    | RunScript ScriptName
    | SaveFile Bool FilePath        -- Bool = whether to dump code/lemma between commands
    | SaveScript FilePath ScriptName
    | ScriptToRewrite RewriteName ScriptName
    | SeqMeta [ScriptEffect]
    deriving Typeable

instance Extern ScriptEffect where
    type Box ScriptEffect = ScriptEffect
    box i = i
    unbox i = i

-- | A composite meta-command for running a loaded script immediately.
--   The script is given the same name as the filepath.
loadAndRun :: FilePath -> ScriptEffect
loadAndRun fp = SeqMeta [LoadFile fp fp, RunScript fp]

runScript :: MonadState CommandLineState m => (ExprH -> m ()) -> m ()
runScript run = go
    where go = popScriptLine >>= maybe (return ()) (\e -> run e >> go)

popScriptLine :: MonadState CommandLineState m => m (Maybe ExprH)
popScriptLine = gets cl_running_script >>= maybe (return Nothing)
                                                 (\case []     -> setRunningScript Nothing >> return Nothing
                                                        (e:es) -> setRunningScript (Just es) >> return (Just e))

pushScriptLine :: MonadState CommandLineState m => ExprH -> m ()
pushScriptLine = pushScript . (:[])

pushScript :: MonadState CommandLineState m => Script -> m ()
pushScript es = modify $ \ st -> st { cl_running_script = Just $ maybe es (++es) (cl_running_script st) }

getFragment :: (MonadCatch m, CLMonad m) => Bool -> AST -> m String
getFragment False _  = return ""
getFragment True ast = do
    (now,opts) <- gets (cl_cursor &&& cl_pretty_opts)
    modify $ setCursor ast
    ps <- getProofStackEmpty
    let discardProvens [] = []
        discardProvens r@(Unproven{} : _) = r
        discardProvens (_:r) = discardProvens r
    doc <- case discardProvens ps of
            Unproven _ (Lemma q _ _ _) _ ls p : _ -> do
                as <- case ls of
                        [] -> return []
                        _  -> liftM (PP.text "Assumed lemmas: " :) $
                                queryInFocus ((liftPrettyH opts $
                                                forM ls $ \(n',l') ->
                                                    return l' >>> ppLemmaT Clean.pretty n'
                                              ) :: TransformH Core [DocH]) Never
                d <- queryInFocus (liftPrettyH opts $
                                    return q >>> extractT (pathT (pathStack2Path p) (ppLCoreTCT Clean.pretty)) :: TransformH Core DocH) Never
                return $ PP.vcat $ as ++ [PP.text "Goal:", d]
            _                             -> queryInFocus (liftPrettyH opts $ pCoreTC Clean.pretty) Never
    let ASCII str = renderCode opts doc
        str' = unlines $ ("" :) $ map ("-- " ++) $ lines str
    modify $ setCursor now
    return str'

fileToScript :: CLMonad m => FilePath -> m Script
fileToScript fileName = do
    putStrToConsole $ "Loading \"" ++ fileName ++ "\"..."
    res <- liftIO $ try (readFile fileName)
    case res of
        Left (err :: IOException) -> fail ("IO error: " ++ show err)
        Right str -> parseScriptCLT str

performScriptEffect :: (MonadCatch m, CLMonad m) => ScriptEffect -> m ()
performScriptEffect = go
    where go (SeqMeta ms) = mapM_ go ms
          go (LoadFile scriptName fileName) = do
            script <- fileToScript fileName
            modify $ \ st -> st {cl_scripts = (scriptName,script) : cl_scripts st}
            putStrToConsole ("Script \"" ++ scriptName ++ "\" loaded successfully from \"" ++ fileName ++ "\".")

          go (SaveFile verb fileName) = do
            putStrToConsole $ "[saving " ++ fileName ++ "]"
            (k,cur) <- gets (cl_kernel &&& cl_cursor)
            all_asts <- listK k
            let m = M.fromList [ (ast,(msg,p)) | (ast,msg,p) <- all_asts ]
                follow ast
                    | Just (msg, p) <- M.lookup ast m = do
                        f <- getFragment verb ast
                        (ls,lastFrag) <- maybe (return ([],"")) follow p
                        let g = if f == lastFrag then id else (f:)
                        return (g $ maybe (maybe id (const ("-- missing command!":)) p) (:) msg ls, f)
                    | otherwise = return ([],"")
            -- no checks to see if you are clobering; be careful
            ls <- fst <$> follow cur
            liftIO $ writeFile fileName $ unlines $ reverse ls

          go (ScriptToRewrite rewriteName scriptName) = do
            script <- lookupScript scriptName
            addScriptToDict rewriteName script
            putStrToConsole ("Rewrite \"" ++ rewriteName ++ "\" defined successfully.")

          go (DefineScript scriptName str) = do
            script <- parseScriptCLT str
            modify $ \ st -> st {cl_scripts = (scriptName,script) : cl_scripts st}
            putStrToConsole ("Script \"" ++ scriptName ++ "\" defined successfully.")

          go (RunScript scriptName) = do
            script <- lookupScript scriptName
            running_script_st <- gets cl_running_script
            setRunningScript $ case running_script_st of
                                Nothing -> Just script
                                Just es -> Just (script ++ es)

          go (SaveScript fileName scriptName) = do
            script <- lookupScript scriptName
            putStrToConsole $ "Saving script \"" ++ scriptName ++ "\" to file \"" ++ fileName ++ "\"."
            liftIO $ writeFile fileName $ unparseScript script
            putStrToConsole $ "Save successful."

lookupScript :: MonadState CommandLineState m => ScriptName -> m Script
lookupScript scriptName = do scripts <- gets cl_scripts
                             case lookup scriptName scripts of
                               Nothing     -> fail $ "No script of name " ++ scriptName ++ " is loaded."
                               Just script -> return script

parseScriptCLT :: Monad m => String -> m Script
parseScriptCLT = either fail return . parseScript

------------------------------------

data UnscopedScriptR
              = ScriptBeginScope
              | ScriptEndScope
              | ScriptPrimUn PrimScriptR
              | ScriptUnsupported String

data ScopedScriptR
              = ScriptScope [ScopedScriptR]
              | ScriptPrimSc ExprH PrimScriptR

data PrimScriptR
       = ScriptRewriteHCore (RewriteH Core)
       | ScriptPath PathH
       | ScriptTransformHCorePath (TransformH Core LocalPathH)


-- TODO: Hacky parsing, needs cleaning up
unscopedToScopedScriptR :: forall m. Monad m => [(ExprH, UnscopedScriptR)] -> m [ScopedScriptR]
unscopedToScopedScriptR = parse
  where
    parse :: [(ExprH, UnscopedScriptR)] -> m [ScopedScriptR]
    parse []     = return []
    parse (y:ys) = case y of
                     (e, ScriptUnsupported msg) -> fail $ mkMsg e msg
                     (e, ScriptPrimUn pr)       -> (ScriptPrimSc e pr :) <$> parse ys
                     (_, ScriptBeginScope)      -> do (rs,zs) <- parseUntilEndScope ys
                                                      (ScriptScope rs :) <$> parse zs
                     (_, ScriptEndScope)        -> fail "unmatched end-of-scope."

    parseUntilEndScope :: Monad m => [(ExprH, UnscopedScriptR)] -> m ([ScopedScriptR], [(ExprH, UnscopedScriptR)])
    parseUntilEndScope []     = fail "missing end-of-scope."
    parseUntilEndScope (y:ys) = case y of
                                  (_, ScriptEndScope)        -> return ([],ys)
                                  (_, ScriptBeginScope)      -> do (rs,zs)  <- parseUntilEndScope ys
                                                                   first (ScriptScope rs :) <$> parseUntilEndScope zs
                                  (e, ScriptPrimUn pr)       -> first (ScriptPrimSc e pr :) <$> parseUntilEndScope ys
                                  (e, ScriptUnsupported msg) -> fail $ mkMsg e msg

    mkMsg :: ExprH -> String -> String
    mkMsg e msg = "script cannot be converted to a rewrite because it contains the following " ++ msg ++ ": " ++ unparseExprH e

-----------------------------------

interpScriptR :: Monad m => [Interp m UnscopedScriptR]
interpScriptR =
  [ interp (\ (RewriteCoreBox r)           -> ScriptPrimUn $ ScriptRewriteHCore r)
  , interp (\ (RewriteCoreTCBox _)         -> ScriptUnsupported "rewrite that traverses types and coercions") -- TODO
  , interp (\ (BiRewriteCoreBox br)        -> ScriptPrimUn $ ScriptRewriteHCore $ whicheverR br)
  , interp (\ (CrumbBox cr)                -> ScriptPrimUn $ ScriptPath [cr])
  , interp (\ (PathBox p)                  -> ScriptPrimUn $ ScriptPath (snocPathToPath p))
  , interp (\ (TransformCorePathBox t)     -> ScriptPrimUn $ ScriptTransformHCorePath t)
  , interp (\ (effect :: KernelEffect)     -> case effect of
                                                BeginScope -> ScriptBeginScope
                                                EndScope   -> ScriptEndScope
                                                _          -> ScriptUnsupported "Kernel effect" )
  , interp (\ (_ :: ShellEffect)           -> ScriptUnsupported "shell effect")
  , interp (\ (_ :: QueryFun)              -> ScriptUnsupported "query")
  , interp (\ (TransformCoreStringBox _)   -> ScriptUnsupported "query")
  , interp (\ (TransformCoreTCStringBox _) -> ScriptUnsupported "query")
  , interp (\ (TransformCoreCheckBox _)    -> ScriptUnsupported "predicate")
  , interp (\ (StringBox _)                -> ScriptUnsupported "message")
  ]

-----------------------------------

scopedScriptsToRewrite :: [ScopedScriptR] -> RewriteH Core
scopedScriptsToRewrite []        = idR
scopedScriptsToRewrite (x : xs)  = let rest = scopedScriptsToRewrite xs
                                       failWith e = prefixFailMsg ("Error in script expression: " ++ unparseExprH e ++ "\n")
                                   in case x of
                                        ScriptScope ys    -> scopedScriptsToRewrite ys >>> rest
                                        ScriptPrimSc e pr -> case pr of
                                                              ScriptRewriteHCore r       -> failWith e r >>> rest
                                                              ScriptPath p               -> failWith e $ pathR p rest
                                                              ScriptTransformHCorePath t -> do p <- failWith e t
                                                                                               localPathR p rest

-----------------------------------

scriptToRewrite :: CLMonad m => Script -> m (RewriteH Core)
scriptToRewrite scr = do
    unscoped <- mapM (interpExprH interpScriptR) scr
    scoped   <- unscopedToScopedScriptR $ zip scr unscoped
    return $ scopedScriptsToRewrite scoped

-----------------------------------

-- | Insert a script into the 'Dictionary'.
addScriptToDict :: CLMonad m => ScriptName -> Script -> m ()
addScriptToDict nm scr = do
    r <- scriptToRewrite scr

    let ext = external nm r [ "User-loaded script." ]

    modify $ \ st -> st { cl_externals = ext : cl_externals st }

-----------------------------------

