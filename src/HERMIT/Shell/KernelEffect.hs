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
import HERMIT.Kernel
import HERMIT.Kure
import HERMIT.Lemma
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

applyRewrite :: (MonadCatch m, CLMonad m) => RewriteH LCoreTC -> ExprH -> m ()
applyRewrite rr expr = do
    ps <- getProofStackEmpty
    let str = unparseExprH expr
    case ps of
        todo@(Unproven {}) : todos -> do
            q' <- queryInFocus (inProofFocusR todo (promoteR rr) >>> (contextfreeT (applyT lintQuantifiedT (ptContext todo)) >> idR) :: TransformH Core Quantified) (Always str)
            let todo' = todo { ptLemma = (ptLemma todo) { lemmaQ = q' } }
            modify $ \ st -> st { cl_proofstack = M.insert (cl_cursor st) (todo':todos) (cl_proofstack st) }
        _ -> do
            (k,(kEnv,(ast,cl))) <- gets (cl_kernel &&& cl_kernel_env &&& cl_cursor &&& cl_corelint)

            rr' <- addFocusR (extractR rr :: RewriteH CoreTC)
            ast' <- prefixFailMsg "Rewrite failed:" $ applyK k rr' (Always str) kEnv ast

            when cl $ do
                warns <- liftM snd (queryK k lintModuleT Never kEnv ast')
                            `catchM` (\ errs -> deleteK k ast' >> fail errs)
                putStrToConsole warns

            addAST ast'

setPath :: (Injection a LCoreTC, MonadCatch m, CLMonad m) => TransformH a LocalPathH -> ExprH -> m ()
setPath t expr = do
    p <- prefixFailMsg "Cannot find path: " $ queryInContext (promoteT t) (Always $ unparseExprH expr)
    modifyLocalPath (<> p)

goDirection :: (MonadCatch m, CLMonad m) => Direction -> ExprH -> m ()
goDirection dir expr = do
    ps <- getProofStackEmpty
    let str = unparseExprH expr
    st <- get
    let k = cl_kernel st
        ast = cl_cursor st
    case ps of
        Unproven {} : _ -> do
            -- TODO: test the path for validity
            addAST =<< tellK k str ast
            modifyLocalPath (moveLocally dir)
        _ -> do -- not in proof shell, so modify normal path stack
            (base, rel) <- getPathStack
            let env = cl_kernel_env st
                rel' = moveLocally dir rel
            (ast',b) <- queryK k (testPathStackT base rel') Never env ast
            if b
            then do addAST =<< tellK k str ast'
                    modifyLocalPath (const rel')
            else fail "invalid path."

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
        Unproven nm l c ls (base,p) : todos -> do
            addAST =<< logExpr
            let todos' = Unproven nm l c ls (p : base, mempty) : todos
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
        Unproven nm l c ls (base,_) : todos -> do
            case base of
                [] -> fail "no scope to end."
                (p:base') -> do
                    addAST =<< logExpr
                    let todos' = Unproven nm l c ls (base', p) : todos
                    modify $ \ st -> st { cl_proofstack = M.insert (cl_cursor st) todos' (cl_proofstack st) }
        _ -> fail "endScope: impossible case!"

deleteAST :: (MonadCatch m, CLMonad m) => AST -> m ()
deleteAST ast = gets cl_kernel >>= flip deleteK ast

-------------------------------------------------------------------------------
