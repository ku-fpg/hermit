{-# LANGUAGE RankNTypes #-}
module Language.HERMIT.Kernel.Command (CommandKernel(..), CAST(..), commandKernel) where

import Control.Concurrent.STM

import qualified Data.IntMap as I

import GhcPlugins

import Language.HERMIT.HermitKure
import Language.HERMIT.Kernel

data CommandKernel = CommandKernel
        { resumeS     ::            CAST                      -> IO ()
        , abortS      ::                                        IO ()
        , applyS      ::            CAST -> RewriteH Core     -> IO CAST
        , queryS      :: forall a . CAST -> TranslateH Core a -> IO a
        , deleteS     ::            CAST                      -> IO ()
        , listS       ::                                        IO [CAST]
        , modPathS    ::            CAST -> (Path -> Path)    -> IO CAST
        , beginScopeS ::            CAST                      -> IO CAST
        , endScopeS   ::            CAST                      -> IO CAST
        }

data CAST = CAST Int
    deriving (Eq, Ord, Show)

-- path stack, representing the base path, then the relative path
type CASTStore = I.IntMap (AST, [Path], Path)

get :: Monad m => Int -> CASTStore -> m (AST, [Path], Path)
get zst m = maybe (fail "commandKernel: invalid CAST") return (I.lookup zst m)

pathStackToLens :: [Path] -> Path -> LensH Core Core
pathStackToLens base = pathL . (concat (reverse base) ++)

commandKernel :: (CommandKernel -> CAST -> IO ()) -> ModGuts -> CoreM ModGuts
commandKernel callback = hermitKernel $ \ kernel initAST -> do
    store <- newTMVarIO $ I.fromList [(0,(initAST, [], []))]
    key <- newTMVarIO (1::Int)

    let newKey = do
            k <- takeTMVar key
            putTMVar key (k+1)
            return k

        ckernel = CommandKernel
            { resumeS     = \ (CAST zst) -> do
                                m <- atomically $ readTMVar store
                                (ast,_,_) <- get zst m
                                resumeK kernel ast
            , abortS      = abortK kernel
            , applyS      = \ (CAST zst) rr -> do
                                m <- atomically $ takeTMVar store
                                (ast, base, rel) <- get zst m
                                ast' <- applyK kernel ast (focusR (pathStackToLens base rel) rr)
                                atomically $ do
                                    k <- newKey
                                    putTMVar store $ I.insert k (ast', base, rel) m
                                    return $ CAST k
            , queryS      = \ (CAST zst) t -> do
                                m <- atomically $ readTMVar store
                                (ast, base, rel) <- get zst m
                                queryK kernel ast (focusT (pathStackToLens base rel) t)
            , deleteS     = \ (CAST zst) -> atomically $ do
                                m <- takeTMVar store
                                putTMVar store $ I.delete zst m
            , listS       = do m <- atomically $ readTMVar store
                               return [ CAST zst | zst <- I.keys m ]
            , modPathS    = \ (CAST zst) f -> do
                                m <- atomically $ takeTMVar store
                                (ast, base, rel) <- get zst m
                                let rel' = f rel
                                condM (fmap (&& (rel /= rel')) (queryK kernel ast (testLensT (pathStackToLens base rel'))))
                                      (atomically $ do
                                            k <- newKey
                                            putTMVar store $ I.insert k (ast, base, rel') m
                                            return $ CAST k)
                                      (atomically $ putTMVar store m >> return (CAST zst)) -- throw error too?
            , beginScopeS = \ (CAST zst) -> atomically $ do
                                m <- takeTMVar store
                                (ast, base, rel) <- get zst m
                                k <- newKey
                                putTMVar store $ I.insert k (ast, rel : base, []) m
                                return $ CAST k
            , endScopeS   = \ (CAST zst) -> atomically $ do
                                m <- takeTMVar store
                                (ast, base, _) <- get zst m
                                case base of
                                    [] -> fail "commandKernel: no scope to end" -- will this fail undo the takeTMVar?
                                    (rel:base') -> do
                                        k <- newKey
                                        putTMVar store $ I.insert k (ast, base', rel) m
                                        return $ CAST k
            }

    callback ckernel $ CAST 0
