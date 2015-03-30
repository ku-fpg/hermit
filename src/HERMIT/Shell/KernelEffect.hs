{-# LANGUAGE ConstraintKinds, DeriveDataTypeable, FlexibleContexts, LambdaCase, TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}

module HERMIT.Shell.KernelEffect
    ( KernelEffect(..)
    , performKernelEffect
    , applyRewrite
    , setPath
    ) where

import Control.Arrow
import Control.Monad.Reader
import Control.Monad.State

import qualified Data.Map as M
import Data.Monoid
import Data.Typeable

import HERMIT.Context
import HERMIT.Dictionary
import HERMIT.External
import HERMIT.Kernel
import HERMIT.Kure
import HERMIT.Lemma
import HERMIT.Parser
import HERMIT.Plugin.Types

import HERMIT.Shell.Types

-------------------------------------------------------------------------------

-- | KernelEffects are things that affect the state of the Kernel
data KernelEffect = Direction Direction -- Move up or top.
                  | BeginScope          -- Begin scope.
                  | EndScope            -- End scope.
                  | Delete AST          -- Delete an AST
   deriving Typeable

instance Extern KernelEffect where
   type Box KernelEffect = KernelEffect
   box i = i
   unbox i = i

performKernelEffect :: (MonadCatch m, CLMonad m) => ExprH -> KernelEffect -> m ()
performKernelEffect e = \case
                            Direction d -> goUp d e
                            BeginScope  -> beginScope e
                            EndScope    -> endScope e
                            Delete sast -> deleteAST sast

-------------------------------------------------------------------------------

applyRewrite :: (MonadCatch m, CLMonad m) => RewriteH LCoreTC -> ExprH -> m ()
applyRewrite rr expr = do
    ps <- getProofStackEmpty
    let str = unparseExprH expr
    case ps of
        todo@(Unproven {}) : todos -> do
            cl' <- queryInFocus (inProofFocusR todo (promoteR rr) >>> (contextfreeT (applyT lintClauseT (ptContext todo)) >> idR) :: TransformH Core Clause) (Always str)
            let todo' = todo { ptLemma = (ptLemma todo) { lemmaC = cl' } }
            modify $ \ st -> st { cl_proofstack = M.insert (cl_cursor st) (todo':todos) (cl_proofstack st) }
        _ -> do
            k <- asks pr_kernel
            (kEnv,(ast,cl)) <- gets (cl_kernel_env &&& cl_cursor &&& cl_corelint)

            rr' <- addFocusR (extractR rr :: RewriteH CoreTC)
            ast' <- prefixFailMsg "Rewrite failed:" $ applyK k rr' (Always str) kEnv ast

            when cl $ do
                warns <- liftM snd (queryK k lintModuleT Never kEnv ast')
                            `catchM` (\ errs -> deleteK k ast' >> fail errs)
                putStrToConsole warns

            addAST ast'
    showWindow Nothing

setPath :: (Injection a LCoreTC, MonadCatch m, CLMonad m) => TransformH a LocalPathH -> ExprH -> m ()
setPath t expr = do
    p <- prefixFailMsg "Cannot find path: " $ queryInContext (promoteT t) Never
    modifyLocalPath (<> p) expr
    showWindow Nothing

goUp :: (MonadCatch m, CLMonad m) => Direction -> ExprH -> m ()
goUp T expr = modifyLocalPath (const mempty) expr
goUp U expr = do
    ps <- getProofStackEmpty
    (_,rel) <- case ps of
                [] -> getPathStack
                todo:_ -> return $ ptPath todo
    case rel of
        SnocPath [] -> fail "cannot move up, at root of scope."
        SnocPath (_:cs) -> modifyLocalPath (const $ SnocPath cs) expr
    showWindow Nothing

beginScope :: (MonadCatch m, CLMonad m) => ExprH -> m ()
beginScope expr = do
    ps <- getProofStackEmpty
    let logExpr = do
            k <- asks pr_kernel
            ast <- gets cl_cursor
            tellK k (unparseExprH expr) ast
    case ps of
        [] -> do
            (base, rel) <- getPathStack
            addAST =<< logExpr
            modify $ \ st -> st { cl_foci = M.insert (cl_cursor st) (rel : base, mempty) (cl_foci st) }
        Unproven nm l c (base,p) : todos -> do
            addAST =<< logExpr
            let todos' = Unproven nm l c (p : base, mempty) : todos
            modify $ \ st -> st { cl_proofstack = M.insert (cl_cursor st) todos' (cl_proofstack st) }
    showWindow Nothing

endScope :: (MonadCatch m, CLMonad m) => ExprH -> m ()
endScope expr = do
    ps <- getProofStackEmpty
    let logExpr = do
            k <- asks pr_kernel
            ast <- gets cl_cursor
            tellK k (unparseExprH expr) ast
    case ps of
        [] -> do
            (base, _) <- getPathStack
            case base of
                [] -> fail "no scope to end."
                (rel:base') -> do
                    addAST =<< logExpr
                    modify $ \ st -> st { cl_foci = M.insert (cl_cursor st) (base', rel) (cl_foci st) }
        Unproven nm l c (base,_) : todos -> do
            case base of
                [] -> fail "no scope to end."
                (p:base') -> do
                    addAST =<< logExpr
                    let todos' = Unproven nm l c (base', p) : todos
                    modify $ \ st -> st { cl_proofstack = M.insert (cl_cursor st) todos' (cl_proofstack st) }
    showWindow Nothing

deleteAST :: (MonadCatch m, CLMonad m) => AST -> m ()
deleteAST ast = asks pr_kernel >>= flip deleteK ast

-------------------------------------------------------------------------------
