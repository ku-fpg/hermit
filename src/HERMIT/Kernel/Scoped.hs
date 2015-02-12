{-# LANGUAGE RankNTypes, FlexibleContexts, InstanceSigs #-}
module HERMIT.Kernel.Scoped
    ( Direction(..)
    , LocalPath
    , moveLocally
    , ScopedKernel(..)
    , SAST(..)
    , scopedKernel
    ) where

import Control.Arrow
import Control.Concurrent.STM
import Control.Exception (bracketOnError)
import Control.Monad
import Control.Monad.IO.Class

import Data.Maybe (fromMaybe)
import Data.Monoid (mempty)
import qualified Data.IntMap as I

import HERMIT.Core
import HERMIT.Context
import HERMIT.Kure
import HERMIT.GHC hiding (Direction,L)
import HERMIT.Kernel

----------------------------------------------------------------------------

-- | A primitive means of denoting navigation of a tree (within a local scope).
data Direction = L -- ^ Left
               | R -- ^ Right
               | U -- ^ Up
               | T -- ^ Top
               deriving (Eq,Show)

pathStack2Paths :: [LocalPath crumb] -> LocalPath crumb -> [Path crumb]
pathStack2Paths ps p = reverse (map snocPathToPath (p:ps))

-- | Movement confined within the local scope.
moveLocally :: Direction -> LocalPathH -> LocalPathH
moveLocally d (SnocPath p) = case p of
                               []     -> mempty
                               cr:crs -> case d of
                                           T -> mempty
                                           U -> SnocPath crs
                                           L -> SnocPath (fromMaybe cr (deprecatedLeftSibling cr)  : crs)
                                           R -> SnocPath (fromMaybe cr (deprecatedRightSibling cr) : crs)


pathStackToLens :: (Injection ModGuts g, Walker HermitC g) => [LocalPathH] -> LocalPathH -> LensH ModGuts g
pathStackToLens ps p = injectL >>> pathL (concat $ pathStack2Paths ps p)

-- This function is used to check the validity of paths, so which sum type we use is important.
testPathStackT :: [LocalPathH] -> LocalPathH -> TransformH ModGuts Bool
testPathStackT ps p = testLensT (pathStackToLens ps p :: LensH ModGuts CoreTC)

----------------------------------------------------------------------------

-- | An alternative HERMIT kernel, that provides scoping.
data ScopedKernel = ScopedKernel
    { resumeS      :: (MonadIO m, MonadCatch m) =>               SAST -> m ()
    , abortS       ::  MonadIO m                =>                       m ()
    , applyS       :: (MonadIO m, MonadCatch m, Injection ModGuts g, Walker HermitC g)
                   => RewriteH g     -> KernelEnv ->             SAST -> m SAST
    , queryS       :: (MonadIO m, MonadCatch m, Injection ModGuts g, Walker HermitC g)
                   => TransformH g a -> KernelEnv ->             SAST -> m (SAST, a)
    , deleteS      :: (MonadIO m, MonadCatch m) =>               SAST -> m ()
    , listS        ::  MonadIO m                =>                       m [SAST]
    , pathS        :: (MonadIO m, MonadCatch m) =>               SAST -> m [PathH]
    , modPathS     :: (MonadIO m, MonadCatch m)
                   => (LocalPathH -> LocalPathH) -> KernelEnv -> SAST -> m SAST
    , beginScopeS  :: (MonadIO m, MonadCatch m) =>               SAST -> m SAST
    , endScopeS    :: (MonadIO m, MonadCatch m) =>               SAST -> m SAST
    -- means of accessing the underlying kernel, obviously for unsafe purposes
    , kernelS      ::                                                    Kernel
    , toASTS       :: (MonadIO m, MonadCatch m) =>               SAST -> m AST
    }

-- | A /handle/ for an 'AST' combined with scoping information.
newtype SAST = SAST Int deriving (Eq, Ord, Show)

-- path stack, representing the base path, then the relative path
type SASTStore = I.IntMap (AST, [LocalPathH], LocalPathH)

get :: Monad m => Int -> SASTStore -> m (AST, [LocalPathH], LocalPathH)
get sAst m = maybe (fail "scopedKernel: invalid SAST") return (I.lookup sAst m)

-- | Ensures that the TMVar is replaced when an error is thrown, and all exceptions are lifted into MonadCatch failures.
safeTakeTMVar :: (MonadCatch m, MonadIO m) => TMVar a -> (a -> IO b) -> m b
safeTakeTMVar mvar = liftAndCatchIO . bracketOnError (atomically $ takeTMVar mvar) (atomically . putTMVar mvar)

-- | Start a HERMIT client by providing an IO function that takes the initial 'ScopedKernel' and inital 'SAST' handle.
--   The 'Modguts' to 'CoreM' Modguts' function required by GHC Plugins is returned.
scopedKernel :: (ScopedKernel -> SAST -> IO ()) -> ModGuts -> CoreM ModGuts
scopedKernel callback = hermitKernel $ \ kernel initAST -> do
    store <- newTMVarIO $ I.fromList [(0,(initAST, [], mempty))]
    key <- newTMVarIO (1::Int)

    let newKey = do
            k <- takeTMVar key
            putTMVar key (k+1)
            return k

        skernel = ScopedKernel
            { resumeS     = \ (SAST sAst) -> liftAndCatchIO $ do
                                m <- atomically $ readTMVar store
                                (ast,_,_) <- get sAst m
                                resumeK kernel ast
            , abortS      = liftIO $ abortK kernel
            , applyS      = \ rr env (SAST sAst) -> safeTakeTMVar store $ \ m -> do
                                (ast, base, rel) <- get sAst m
                                applyK kernel ast (focusR (pathStackToLens base rel) rr) env
                                  >>= runKureM (\ ast' -> atomically $ do
                                                    k <- newKey
                                                    putTMVar store $ I.insert k (ast', base, rel) m
                                                    return (SAST k))
                                               fail
            , queryS      = \ t env (SAST sAst) -> safeTakeTMVar store $ \ m -> do
                                (ast, base, rel) <- get sAst m
                                queryK kernel ast (focusT (pathStackToLens base rel) t) env
                                  >>= runKureM (\ (ast',r) -> atomically $
                                                    if (ast == ast')
                                                    then do putTMVar store m
                                                            return (SAST sAst, r)
                                                    else do k <- newKey
                                                            putTMVar store $ I.insert k (ast', base, rel) m
                                                            return (SAST k, r))
                                               fail
            , deleteS     = \ (SAST sAst) -> safeTakeTMVar store $ \ m -> do
                                (ast,_,_) <- get sAst m
                                let m' = I.delete sAst m
                                    fst3 (x,_,_) = x
                                    asts = I.foldr ((:) . fst3) [] m'
                                when (ast `notElem` asts) $ deleteK kernel ast
                                atomically $ putTMVar store m'
            , listS       = do m <- liftIO $ atomically $ readTMVar store
                               return [ SAST sAst | sAst <- I.keys m ]
            , pathS       = \ (SAST sAst) -> liftAndCatchIO $ do
                                m <- atomically $ readTMVar store
                                (_, base, rel) <- get sAst m
                                return $ pathStack2Paths base rel
            , modPathS    = \ f env (SAST sAst) -> safeTakeTMVar store $ \ m -> do
                                (ast, base, rel) <- get sAst m
                                let rel' = f rel
                                queryK kernel ast (testPathStackT base rel') env
                                  >>= runKureM (\ (_,b) -> if rel == rel'
                                                           then fail "Path is unchanged, nothing to do."
                                                           else if b
                                                                then atomically $ do k <- newKey
                                                                                     putTMVar store $ I.insert k (ast, base, rel') m
                                                                                     return $ SAST k
                                                                else fail "Invalid path created.")
                                               fail
            , beginScopeS = \ (SAST sAst) -> safeTakeTMVar store $ \m -> do
                                (ast, base, rel) <- get sAst m
                                atomically $ do k <- newKey
                                                putTMVar store $ I.insert k (ast, rel : base, mempty) m
                                                return $ SAST k
            , endScopeS   = \ (SAST sAst) -> safeTakeTMVar store $ \m -> do
                                (ast, base, _) <- get sAst m
                                case base of
                                    []          -> fail "Scoped Kernel: no scope to end."
                                    rel : base' -> atomically $ do k <- newKey
                                                                   putTMVar store $ I.insert k (ast, base', rel) m
                                                                   return $ SAST k
            , kernelS     = kernel
            , toASTS      = \ (SAST sAst) -> liftAndCatchIO $ do
                                m <- atomically $ readTMVar store
                                (ast, _, _) <- get sAst m
                                return ast
            }

    callback skernel $ SAST 0
