{-# LANGUAGE ScopedTypeVariables #-}

module HERMIT.Shell.ImportR
  (  -- * Converting Scripts to Rewrites
     importToDictionary
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

import HERMIT.Shell.Types

------------------------------------

data UnscopedImportR
              = ImportBeginScope
              | ImportEndScope
              | ImportPrimUn PrimImportR
              | ImportUnsupported

data ScopedImportR
              = ImportScope [ScopedImportR]
              | ImportPrimSc PrimImportR

data PrimImportR
       = ImportRewriteHCore (RewriteH Core)
       | ImportPath PathH
       | ImportTranslateHCorePath (TranslateH Core LocalPathH)


-- TODO: Hacky parsing, needs cleaning up
unscopedToScopedImportR :: forall m. Monad m => [UnscopedImportR] -> m [ScopedImportR]
unscopedToScopedImportR = parse
  where
    parse :: [UnscopedImportR] -> m [ScopedImportR]
    parse []     = return []
    parse (y:ys) = case y of
                     ImportUnsupported -> fail "unsupported AST effect."
                     ImportPrimUn pr   -> (ImportPrimSc pr :) <$> parse ys
                     ImportBeginScope  -> do (rs,zs) <- parseUntilEndScope ys
                                             (ImportScope rs :) <$> parse zs
                     ImportEndScope    -> fail "unmatched end-of-scope."

    parseUntilEndScope :: Monad m => [UnscopedImportR] -> m ([ScopedImportR], [UnscopedImportR])
    parseUntilEndScope []     = fail "missing end-of-scope."
    parseUntilEndScope (y:ys) = case y of
                                  ImportEndScope    -> return ([],ys)
                                  ImportBeginScope  -> do (rs,zs)  <- parseUntilEndScope ys
                                                          first (ImportScope rs :) <$> parseUntilEndScope zs
                                  ImportPrimUn pr   -> first (ImportPrimSc pr :) <$> parseUntilEndScope ys
                                  ImportUnsupported -> fail "unsupported AST effect."

-----------------------------------

interpImportR :: [Interp UnscopedImportR]
interpImportR =
                [ interp (\ (RewriteCoreBox r)        -> ImportPrimUn $ ImportRewriteHCore r)
                , interp (\ (CrumbBox cr)             -> ImportPrimUn $ ImportPath [cr])
                , interp (\ (PathBox p)               -> ImportPrimUn $ ImportPath (snocPathToPath p))
                , interp (\ (TranslateCorePathBox t)  -> ImportPrimUn $ ImportTranslateHCorePath t)
                , interp (\ (effect :: AstEffect)     -> case effect of
                                                           BeginScope -> ImportBeginScope
                                                           EndScope   -> ImportEndScope
                                                           _          -> ImportUnsupported ) -- TODO: Sort out how we handle unsupported AstEffects so we can produce decent error messages.
                ]

-----------------------------------

scopedImportsToRewrite :: [ScopedImportR] -> RewriteH Core
scopedImportsToRewrite []        = idR
scopedImportsToRewrite (x : xs)  = let rest = scopedImportsToRewrite xs
                                   in case x of
                                        ImportScope ys   -> scopedImportsToRewrite ys >>> rest
                                        ImportPrimSc pr  -> case pr of
                                                              ImportRewriteHCore r       -> r >>> rest
                                                              ImportPath p               -> pathR p rest
                                                              ImportTranslateHCorePath t -> do p <- t
                                                                                               localPathR p rest

-----------------------------------

-----------------------------------

rewriteToExternal :: ExternalName -> FilePath -> RewriteH Core -> External
rewriteToExternal nm fp r = external nm r ["This rewrite was imported by the user from " ++ fp]

-----------------------------------

importToDictionary :: Monad m => Dictionary -> Script -> ExternalName -> FilePath -> m Dictionary
importToDictionary dict es nm fp = do unscoped <- mapM (interpExprH dict interpImportR) es
                                      scoped   <- unscopedToScopedImportR unscoped
                                      let ex  = rewriteToExternal nm fp (scopedImportsToRewrite scoped)
                                          dyn = externDyn ex -- TODO: This throws away much of the External information
                                                             --       The new rewrite will not appear in the "help",
                                                             --       because the "help" information is constructed in advance.

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
