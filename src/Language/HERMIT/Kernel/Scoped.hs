{-# LANGUAGE RankNTypes #-}
module Language.HERMIT.Kernel.Scoped (ScopedKernel(..), SAST(..), scopedKernel) where

import Control.Concurrent.STM
import Control.Exception.Base (bracketOnError)

import qualified Data.IntMap as I

import GhcPlugins

import Language.HERMIT.Kure
import Language.HERMIT.Kernel

data ScopedKernel = ScopedKernel
        { resumeS     ::            SAST                      -> IO ()
        , abortS      ::                                         IO ()
        , applyS      ::            SAST -> RewriteH Core     -> IO (KureMonad SAST)
        , queryS      :: forall a . SAST -> TranslateH Core a -> IO (KureMonad a)
        , deleteS     ::            SAST                      -> IO ()
        , listS       ::                                         IO [SAST]
        , pathS       ::            SAST                      -> IO [Path]
        , modPathS    ::            SAST -> (Path -> Path)    -> IO (KureMonad SAST)
        , beginScopeS ::            SAST                      -> IO SAST
        , endScopeS   ::            SAST                      -> IO SAST
        }

data SAST = SAST Int
    deriving (Eq, Ord, Show)

-- path stack, representing the base path, then the relative path
type SASTStore = I.IntMap (AST, [Path], Path)

get :: Monad m => Int -> SASTStore -> m (AST, [Path], Path)
get sAst m = maybe (fail "scopedKernel: invalid SAST") return (I.lookup sAst m)

pathStackToLens :: [Path] -> Path -> LensH Core Core
pathStackToLens base = pathL . (concat (reverse base) ++)

safeTakeTMVar :: TMVar a -> (a -> IO b) -> IO b
safeTakeTMVar mvar = bracketOnError (atomically $ takeTMVar mvar) (atomically . putTMVar mvar)

scopedKernel :: (ScopedKernel -> SAST -> IO ()) -> ModGuts -> CoreM ModGuts
scopedKernel callback = hermitKernel $ \ kernel initAST -> do
    store <- newTMVarIO $ I.fromList [(0,(initAST, [], []))]
    key <- newTMVarIO (1::Int)

    let failCleanup :: SASTStore -> String -> IO (KureMonad a)
        failCleanup m msg = atomically $ do putTMVar store m
                                            return $ fail msg

    let newKey = do
            k <- takeTMVar key
            putTMVar key (k+1)
            return k

        skernel = ScopedKernel
            { resumeS     = \ (SAST sAst) -> do
                                m <- atomically $ readTMVar store
                                (ast,_,_) <- get sAst m
                                resumeK kernel ast
            , abortS      = abortK kernel
            , applyS      = \ (SAST sAst) rr -> safeTakeTMVar store $ \ m -> do
                                (ast, base, rel) <- get sAst m
                                applyK kernel ast (focusR (pathStackToLens base rel) rr)
                                  >>= runKureMonad (\ ast' -> atomically $ do k <- newKey
                                                                              putTMVar store $ I.insert k (ast', base, rel) m
                                                                              return $ return $ SAST k)
                                                   (failCleanup m)
            , queryS      = \ (SAST sAst) t -> do
                                m <- atomically $ readTMVar store
                                (ast, base, rel) <- get sAst m
                                queryK kernel ast (focusT (pathStackToLens base rel) t)
            , deleteS     = \ (SAST sAst) -> atomically $ do
                                m <- takeTMVar store
                                putTMVar store $ I.delete sAst m
            , listS       = do m <- atomically $ readTMVar store
                               return [ SAST sAst | sAst <- I.keys m ]
            , pathS       = \ (SAST sAst) -> atomically $ do
                                m <- readTMVar store
                                (_, base, rel) <- get sAst m
                                return $ reverse $ rel : base
            , modPathS    = \ (SAST sAst) f -> safeTakeTMVar store $ \ m -> do
                                (ast, base, rel) <- get sAst m
                                let rel' = f rel
                                queryK kernel ast (testLensT (pathStackToLens base rel'))
                                  >>= runKureMonad (\ b -> if rel == rel'
                                                            then failCleanup m "Path is unchanged, nothing to do."
                                                            else if b
                                                                  then atomically $ do k <- newKey
                                                                                       putTMVar store $ I.insert k (ast, base, rel') m
                                                                                       return (return $ SAST k)
                                                                  else failCleanup m "Invalid path created.")
                                                   (failCleanup m)
            , beginScopeS = \ (SAST sAst) -> atomically $ do
                                m <- takeTMVar store
                                (ast, base, rel) <- get sAst m
                                k <- newKey
                                putTMVar store $ I.insert k (ast, rel : base, []) m
                                return $ SAST k
            , endScopeS   = \ (SAST sAst) -> atomically $ do
                                m <- takeTMVar store
                                (ast, base, _) <- get sAst m
                                case base of
                                    [] -> fail "scopedKernel: no scope to end"
                                    (rel:base') -> do
                                        k <- newKey
                                        putTMVar store $ I.insert k (ast, base', rel) m
                                        return $ SAST k
            }

    callback skernel $ SAST 0
