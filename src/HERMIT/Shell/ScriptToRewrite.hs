{-# LANGUAGE ScopedTypeVariables #-}

module HERMIT.Shell.ScriptToRewrite
  ( -- * Converting Scripts to Rewrites
    addScriptToDict
  )
where

import Control.Arrow
import Control.Monad (liftM)

import Data.Dynamic
import Data.Map

import HERMIT.Context(LocalPathH)
import HERMIT.Kure
import HERMIT.External
import HERMIT.Interp

import HERMIT.PrettyPrinter.Common(TranslateCoreTCDocHBox(..))
import HERMIT.Shell.Types

------------------------------------

data UnscopedScriptR
              = ScriptBeginScope
              | ScriptEndScope
              | ScriptPrimUn PrimScriptR
              | ScriptUnsupported String

data ScopedScriptR
              = ScriptScope [ScopedScriptR]
              | ScriptPrimSc PrimScriptR

data PrimScriptR
       = ScriptRewriteHCore (RewriteH Core)
       | ScriptPath PathH
       | ScriptTranslateHCorePath (TranslateH Core LocalPathH)


-- TODO: Hacky parsing, needs cleaning up
unscopedToScopedScriptR :: forall m. Monad m => [UnscopedScriptR] -> m [ScopedScriptR]
unscopedToScopedScriptR = parse
  where
    parse :: [UnscopedScriptR] -> m [ScopedScriptR]
    parse []     = return []
    parse (y:ys) = case y of
                     ScriptUnsupported msg -> fail ("script contains " ++ msg ++ " which cannot be converted to a rewrite.")
                     ScriptPrimUn pr       -> (ScriptPrimSc pr :) <$> parse ys
                     ScriptBeginScope      -> do (rs,zs) <- parseUntilEndScope ys
                                                 (ScriptScope rs :) <$> parse zs
                     ScriptEndScope        -> fail "unmatched end-of-scope."

    parseUntilEndScope :: Monad m => [UnscopedScriptR] -> m ([ScopedScriptR], [UnscopedScriptR])
    parseUntilEndScope []     = fail "missing end-of-scope."
    parseUntilEndScope (y:ys) = case y of
                                  ScriptEndScope        -> return ([],ys)
                                  ScriptBeginScope      -> do (rs,zs)  <- parseUntilEndScope ys
                                                              first (ScriptScope rs :) <$> parseUntilEndScope zs
                                  ScriptPrimUn pr       -> first (ScriptPrimSc pr :) <$> parseUntilEndScope ys
                                  ScriptUnsupported msg -> fail ("script contains " ++ msg ++ " which cannot be converted to a rewrite.")

-----------------------------------

interpScriptR :: [Interp UnscopedScriptR]
interpScriptR =
  [ interp (\ (RewriteCoreBox r)           -> ScriptPrimUn $ ScriptRewriteHCore r)
  , interp (\ (RewriteCoreTCBox _)         -> ScriptUnsupported "rewrites that traverse types and coercions") -- TODO
  , interp (\ (BiRewriteCoreBox br)        -> ScriptPrimUn $ ScriptRewriteHCore $ forewardT br)
  , interp (\ (CrumbBox cr)                -> ScriptPrimUn $ ScriptPath [cr])
  , interp (\ (PathBox p)                  -> ScriptPrimUn $ ScriptPath (snocPathToPath p))
  , interp (\ (TranslateCorePathBox t)     -> ScriptPrimUn $ ScriptTranslateHCorePath t)
  , interp (\ (effect :: AstEffect)        -> case effect of
                                                BeginScope -> ScriptBeginScope
                                                EndScope   -> ScriptEndScope
                                                _          -> ScriptUnsupported "AST effects" )
  , interp (\ (_ :: MetaCommand)           -> ScriptUnsupported "meta commands")
  , interp (\ (_ :: ShellEffect)           -> ScriptUnsupported "shell effects")
  , interp (\ (_ :: QueryFun)              -> ScriptUnsupported "queries")
  , interp (\ (TranslateCoreStringBox _)   -> ScriptUnsupported "queries")
  , interp (\ (TranslateCoreTCStringBox _) -> ScriptUnsupported "queries")
  , interp (\ (TranslateCoreTCDocHBox _)   -> ScriptUnsupported "queries")
  , interp (\ (TranslateCoreCheckBox _)    -> ScriptUnsupported "predicates")
  , interp (\ (StringBox _)                -> ScriptUnsupported "messages")
  ]

-----------------------------------

scopedScriptsToRewrite :: [ScopedScriptR] -> RewriteH Core
scopedScriptsToRewrite []        = idR
scopedScriptsToRewrite (x : xs)  = let rest = scopedScriptsToRewrite xs
                                   in case x of
                                        ScriptScope ys   -> scopedScriptsToRewrite ys >>> rest
                                        ScriptPrimSc pr  -> case pr of
                                                              ScriptRewriteHCore r       -> r >>> rest
                                                              ScriptPath p               -> pathR p rest
                                                              ScriptTranslateHCorePath t -> do p <- t
                                                                                               localPathR p rest

-----------------------------------

-----------------------------------

-- | Insert a script into the 'Dictionary'.
addScriptToDict :: Monad m => ScriptName -> Script -> Dictionary -> m Dictionary
addScriptToDict nm scr dict =
  do unscoped <- mapM (interpExprH dict interpScriptR) scr
     scoped   <- unscopedToScopedScriptR unscoped
     let
         dyn = toDyn (box $ scopedScriptsToRewrite scoped)

         alteration :: Maybe [Dynamic] -> Maybe [Dynamic]
         alteration Nothing     = Just [dyn]
         alteration (Just dyns) = Just (dyn:dyns)

     return $ alter alteration nm dict

-----------------------------------

-- I find it annoying that Functor is not a superclass of Monad.
(<$>) :: Monad m => (a -> b) -> m a -> m b
(<$>) = liftM
{-# INLINE (<$>) #-}

-----------------------------------
