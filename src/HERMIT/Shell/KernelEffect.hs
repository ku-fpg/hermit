{-# LANGUAGE ConstraintKinds, DeriveDataTypeable, FlexibleContexts, LambdaCase, TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}

module HERMIT.Shell.KernelEffect
    ( KernelEffect(..)
    , performKernelEffect
    , applyRewrite
    , setPath
    ) where

import Control.Arrow
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

    rr' <- addFocusR rr
    ast' <- prefixFailMsg "Rewrite failed:" $ applyK k rr' (Always (unparseExprH expr)) kEnv ast

    when (cl_corelint st) $ do
        warns <- liftM snd (queryK k lintModuleT Never kEnv ast')
                    `catchM` (\ errs -> deleteK k ast' >> fail errs)
        putStrToConsole warns

    addAST ast'

setPath :: (Injection GHC.ModGuts g, Walker HermitC g, MonadCatch m, CLMonad m)
        => TransformH g LocalPathH -> ExprH -> m ()
setPath t expr = do
    p <- prefixFailMsg "Cannot find path: " $ queryInFocus t (Always $ unparseExprH expr)
    ast <- gets cl_cursor
    addASTWithPath ast (<> p)
    showWindow

goDirection :: (MonadCatch m, CLMonad m) => Direction -> ExprH -> m ()
goDirection dir expr = do
    ps <- getProofStackEmpty
    case ps of
        [] -> do -- not in proof shell, so modify normal path stack
            (base, rel) <- getPathStack
            st <- get
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
        Unproven nm l c ls (base,p) t : todos -> do
            let p' = moveLocally dir p
                todos' = Unproven nm l c ls (base,p') t : todos
            -- TODO: test the path for validity
            modify $ \ st -> st { cl_proofstack = M.insert (cl_cursor st) todos' (cl_proofstack st) }
        _ -> fail "goDirection: impossible case!"

beginScope :: (MonadCatch m, CLMonad m) => ExprH -> m ()
beginScope expr = do
    ps <- getProofStackEmpty
    let logExpr = do
            (k,ast) <- gets (cl_kernel &&& cl_cursor)
            tellK k (unparseExprH expr) ast
    case ps of
        [] -> do
            (base, rel) <- getPathStack
            addAST =<< logExpr
            modify $ \ st -> st { cl_foci = M.insert (cl_cursor st) (rel : base, mempty) (cl_foci st) }
            showWindow
        Unproven nm l c ls (base,p) t : todos -> do
            addAST =<< logExpr
            let todos' = Unproven nm l c ls (p : base, mempty) t : todos
            modify $ \ st -> st { cl_proofstack = M.insert (cl_cursor st) todos' (cl_proofstack st) }
        _ -> fail "beginScope: impossible case!"

endScope :: (MonadCatch m, CLMonad m) => ExprH -> m ()
endScope expr = do
    ps <- getProofStackEmpty
    let logExpr = do
            (k,ast) <- gets (cl_kernel &&& cl_cursor)
            tellK k (unparseExprH expr) ast
    case ps of
        [] -> do
            (base, _) <- getPathStack
            case base of
                [] -> fail "no scope to end."
                (rel:base') -> do
                    addAST =<< logExpr
                    modify $ \ st -> st { cl_foci = M.insert (cl_cursor st) (base', rel) (cl_foci st) }
                    showWindow
        Unproven nm l c ls (base,_) t : todos -> do
            case base of
                [] -> fail "no scope to end."
                (p:base') -> do
                    addAST =<< logExpr
                    let todos' = Unproven nm l c ls (base', p) t : todos
                    modify $ \ st -> st { cl_proofstack = M.insert (cl_cursor st) todos' (cl_proofstack st) }
        _ -> fail "endScope: impossible case!"

deleteAST :: (MonadCatch m, CLMonad m) => AST -> m ()
deleteAST ast = gets cl_kernel >>= flip deleteK ast

-------------------------------------------------------------------------------
