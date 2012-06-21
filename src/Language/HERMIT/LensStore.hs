{-# LANGUAGE RankNTypes #-}
module Language.HERMIT.LensStore (LensStore(..), ZST(..), lensStore) where

import Control.Concurrent.STM

import qualified Data.IntMap as I

import Language.HERMIT.HermitKure
import Language.HERMIT.Kernel

data LensStore = LensStore
        { resumeL     ::            ZST                      -> IO ()
        , abortL      ::                                        IO ()
        , applyL      ::            ZST -> RewriteH Core     -> IO ZST
        , queryL      :: forall a . ZST -> TranslateH Core a -> IO a
        , deleteL     ::            ZST                      -> IO ()
        , listL       ::                                        IO [ZST]
        , modPathL    ::            ZST -> (Path -> Path)    -> IO ZST
        , beginScopeL ::            ZST                      -> IO ZST
        , endScopeL   ::            ZST                      -> IO ZST
        }

data ZST = ZST Int
    deriving (Eq, Ord, Show)

-- path stack, representing the base path, then the relative path
type ZSTStore = I.IntMap (AST, [Path], Path)

get :: Monad m => Int -> ZSTStore -> m (AST, [Path], Path)
get zst m = maybe (fail "lensStore: invalid ZST") return (I.lookup zst m)

pathStackToLens :: [Path] -> Path -> LensH Core Core
pathStackToLens base = pathL . (concat (reverse base) ++)

-- not sure about this interface
-- hermitKernel :: (Kernel -> AST -> IO ()) -> ModGuts -> CoreM ModGuts
-- hermitKernel (lensStore f) where f :: LensStore -> ZST -> IO ()
-- hermitKernel $ lensStore $ \ lenstore zst -> do ...
lensStore :: (LensStore -> ZST -> IO ()) -> Kernel -> AST -> IO ()
lensStore callback kernel initAST = do
    store <- newTMVarIO $ I.fromList [(0,(initAST, [], []))]
    key <- newTMVarIO (1::Int)

    let newKey = do
            k <- takeTMVar key
            putTMVar key (k+1)
            return k

        ls = LensStore
            { resumeL     = \ (ZST zst) -> do
                                m <- atomically $ readTMVar store
                                (ast,_,_) <- get zst m
                                resumeK kernel ast
            , abortL      = abortK kernel
            , applyL      = \ (ZST zst) rr -> do
                                m <- atomically $ takeTMVar store
                                (ast, base, rel) <- get zst m
                                ast' <- applyK kernel ast (focusR (pathStackToLens base rel) rr)
                                atomically $ do
                                    k <- newKey
                                    putTMVar store $ I.insert k (ast', base, rel) m
                                    return $ ZST k
            , queryL      = \ (ZST zst) t -> do
                                m <- atomically $ readTMVar store
                                (ast, base, rel) <- get zst m
                                queryK kernel ast (focusT (pathStackToLens base rel) t)
            , deleteL     = \ (ZST zst) -> atomically $ do
                                m <- takeTMVar store
                                putTMVar store $ I.delete zst m
            , listL       = do m <- atomically $ readTMVar store
                               return [ ZST zst | zst <- I.keys m ]
            , modPathL    = \ (ZST zst) f -> do
                                m <- atomically $ takeTMVar store
                                (ast, base, rel) <- get zst m
                                let rel' = f rel
                                condM (fmap (&& (rel /= rel')) (queryK kernel ast (testLensT (pathStackToLens base rel'))))
                                      (atomically $ do
                                            k <- newKey
                                            putTMVar store $ I.insert k (ast, base, rel') m
                                            return $ ZST k)
                                      (atomically $ putTMVar store m >> return (ZST zst)) -- throw error too?
            , beginScopeL = \ (ZST zst) -> atomically $ do
                                m <- takeTMVar store
                                (ast, base, rel) <- get zst m
                                k <- newKey
                                putTMVar store $ I.insert k (ast, rel : base, []) m
                                return $ ZST k
            , endScopeL   = \ (ZST zst) -> atomically $ do
                                m <- takeTMVar store
                                (ast, base, _) <- get zst m
                                case base of
                                    [] -> fail "lensStore: no scope to end"
                                    (rel:base') -> do
                                        k <- newKey
                                        putTMVar store $ I.insert k (ast, base', rel) m
                                        return $ ZST k
            }

    callback ls $ ZST 0
