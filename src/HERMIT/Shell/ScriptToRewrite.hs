{-# LANGUAGE FlexibleContexts, ScopedTypeVariables #-}

module HERMIT.Shell.ScriptToRewrite
  ( -- * Converting Scripts to Rewrites
    addScriptToDict
  , lookupScript
  , scriptToRewrite
  )
where

import Control.Arrow
import Control.Monad.State

import Data.Dynamic
import Data.Map hiding (lookup)

import HERMIT.Context(LocalPathH)
import HERMIT.Kure
import HERMIT.External
import HERMIT.Parser(Script, ExprH, unparseExprH)

import HERMIT.PrettyPrinter.Common(TranslateCoreTCDocHBox(..))

import HERMIT.Shell.Interpreter
import HERMIT.Shell.Types

------------------------------------

lookupScript :: MonadState CommandLineState m => ScriptName -> m Script
lookupScript scriptName = do scripts <- gets cl_scripts
                             case lookup scriptName scripts of
                               Nothing     -> fail $ "No script of name " ++ scriptName ++ " is loaded."
                               Just script -> return script

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
       | ScriptTranslateHCorePath (TranslateH Core LocalPathH)


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

interpScriptR :: [Interp UnscopedScriptR]
interpScriptR =
  [ interp (\ (RewriteCoreBox r)           -> ScriptPrimUn $ ScriptRewriteHCore r)
  , interp (\ (RewriteCoreTCBox _)         -> ScriptUnsupported "rewrite that traverses types and coercions") -- TODO
  , interp (\ (BiRewriteCoreBox br)        -> ScriptPrimUn $ ScriptRewriteHCore $ whicheverR br)
  , interp (\ (CrumbBox cr)                -> ScriptPrimUn $ ScriptPath [cr])
  , interp (\ (PathBox p)                  -> ScriptPrimUn $ ScriptPath (snocPathToPath p))
  , interp (\ (TranslateCorePathBox t)     -> ScriptPrimUn $ ScriptTranslateHCorePath t)
  , interp (\ (effect :: KernelEffect)     -> case effect of
                                                BeginScope -> ScriptBeginScope
                                                EndScope   -> ScriptEndScope
                                                _          -> ScriptUnsupported "Kernel effect" )
  , interp (\ (_ :: ShellEffect)           -> ScriptUnsupported "shell effect")
  , interp (\ (_ :: QueryFun)              -> ScriptUnsupported "query")
  , interp (\ (TranslateCoreStringBox _)   -> ScriptUnsupported "query")
  , interp (\ (TranslateCoreTCStringBox _) -> ScriptUnsupported "query")
  , interp (\ (TranslateCoreTCDocHBox _)   -> ScriptUnsupported "query")
  , interp (\ (TranslateCoreCheckBox _)    -> ScriptUnsupported "predicate")
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
                                                              ScriptTranslateHCorePath t -> do p <- failWith e t
                                                                                               localPathR p rest

-----------------------------------

scriptToRewrite :: MonadState CommandLineState m => Script -> m (RewriteH Core)
scriptToRewrite scr = do
    unscoped <- mapM (interpExprH interpScriptR) scr
    scoped   <- unscopedToScopedScriptR $ zip scr unscoped
    return $ scopedScriptsToRewrite scoped

-----------------------------------

-- | Insert a script into the 'Dictionary'.
addScriptToDict :: MonadState CommandLineState m => ScriptName -> Script -> m ()
addScriptToDict nm scr = do
    r <- scriptToRewrite scr

    let dyn = toDyn (box r)

        alteration :: Maybe [Dynamic] -> Maybe [Dynamic]
        alteration Nothing     = Just [dyn]
        alteration (Just dyns) = Just (dyn:dyns)

    modify $ \ st -> st { cl_dict = alter alteration nm (cl_dict st) }

-----------------------------------

-- I find it annoying that Functor is not a superclass of Monad.
(<$>) :: Monad m => (a -> b) -> m a -> m b
(<$>) = liftM
{-# INLINE (<$>) #-}

-----------------------------------
