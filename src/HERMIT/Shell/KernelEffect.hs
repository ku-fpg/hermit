{-# LANGUAGE ConstraintKinds, DeriveDataTypeable, FlexibleContexts, LambdaCase, TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}

module HERMIT.Shell.KernelEffect
    ( KernelEffect(..)
    , performKernelEffect
    , applyRewrite
    , setPath
    ) where

import Control.Monad.State

import qualified Data.Map as M
import Data.Monoid
import Data.Typeable

import HERMIT.Context
import HERMIT.Dictionary
import HERMIT.External
import qualified HERMIT.GHC as GHC
import HERMIT.Kernel
import HERMIT.Kure
import HERMIT.Parser

import HERMIT.Plugin.Renderer

import HERMIT.PrettyPrinter.Common

import HERMIT.Shell.Types

-------------------------------------------------------------------------------

-- | KernelEffects are things that affect the state of the Kernel
data KernelEffect = Direction  Direction -- Change the currect location using directions.
                  | BeginScope           -- Begin scope.
                  | EndScope             -- End scope.
                  | Delete     AST       -- Delete an AST
   deriving Typeable

instance Extern KernelEffect where
   type Box KernelEffect = KernelEffect
   box i = i
   unbox i = i

performKernelEffect :: (MonadCatch m, CLMonad m) => ExprH -> KernelEffect -> m ()
performKernelEffect e = \case
                            Direction dir -> goDirection dir e
                            BeginScope    -> beginScope e
                            EndScope      -> endScope e
                            Delete sast   -> deleteAST sast

-------------------------------------------------------------------------------

applyRewrite :: (Injection GHC.ModGuts g, Walker HermitC g, MonadCatch m, CLMonad m)
             => RewriteH g -> ExprH -> m ()
applyRewrite rr expr = do
    st <- get

    let k = cl_kernel st
        kEnv = cl_kernel_env st
        ast = cl_cursor st
        ppOpts = cl_pretty_opts st
        pp = pCoreTC $ cl_pretty st

    rr' <- addFocusR rr
    ast' <- prefixFailMsg "Rewrite failed:" $ applyK k rr' (Always (unparseExprH expr)) kEnv ast

    let showResult = if cl_diffonly st then showDiff else showWindow
        showDiff = do q <- addFocusT $ liftPrettyH ppOpts pp
                      (_,doc1) <- queryK k q Never kEnv ast
                      (_,doc2) <- queryK k q Never kEnv ast'
                      diffDocH (cl_pretty st) doc1 doc2 >>= cl_putStr

    when (cl_corelint st) $ do
        warns <- liftM snd (queryK k lintModuleT Never kEnv ast')
                    `catchM` (\ errs -> deleteK k ast' >> fail errs)
        putStrToConsole warns

    addAST ast' >> showResult

setPath :: (Injection GHC.ModGuts g, Walker HermitC g, MonadCatch m, CLMonad m)
        => TransformH g LocalPathH -> ExprH -> m ()
setPath t expr = do
    p <- prefixFailMsg "Cannot find path: " $ queryInFocus t (Always $ unparseExprH expr)
    ast <- gets cl_cursor
    addASTWithPath ast (<> p)
    showWindow

goDirection :: (MonadCatch m, CLMonad m) => Direction -> ExprH -> m ()
goDirection dir expr = do
    st <- get
    (base, rel) <- getPathStack
    let k = cl_kernel st
        env = cl_kernel_env st
        ast = cl_cursor st
        rel' = moveLocally dir rel
    (ast',b) <- queryK k (testPathStackT base rel') Never env ast
    if b
    then do ast'' <- tellK k (unparseExprH expr) ast'
            addASTWithPath ast'' (const rel')
            showWindow
    else fail "invalid path."

beginScope :: (MonadCatch m, CLMonad m) => ExprH -> m ()
beginScope expr = do
    s <- get
    ast <- tellK (cl_kernel s) (unparseExprH expr) (cl_cursor s)
    (base, rel) <- getPathStack
    modify $ \ st -> st { cl_foci = M.alter (const (Just (rel : base, mempty))) ast (cl_foci st) }
    modify $ setCursor ast
    showWindow

endScope :: (MonadCatch m, CLMonad m) => ExprH -> m ()
endScope expr = do
    (base, _) <- getPathStack
    case base of
        [] -> fail "no scope to end."
        (rel:base') -> do
            s <- get
            ast <- tellK (cl_kernel s) (unparseExprH expr) (cl_cursor s)
            modify $ \ st -> st { cl_foci = M.alter (const (Just (base', rel))) ast (cl_foci st) }
            modify $ setCursor ast
            showWindow

deleteAST :: (MonadCatch m, CLMonad m) => AST -> m ()
deleteAST ast = gets cl_kernel >>= flip deleteK ast

-------------------------------------------------------------------------------
