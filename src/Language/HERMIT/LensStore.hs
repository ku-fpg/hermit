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
        , modPathL    ::            ZST -> (Path -> Path)    -> IO ()
        , scopeStartL ::            ZST                      -> IO ()
        , scopeEndL   ::            ZST                      -> IO ()
        }

data ZST = ZST Int
    deriving (Eq, Ord, Show)

type ZSTStore = I.IntMap (AST, [Path])

get :: Monad m => Int -> ZSTStore -> m (AST, [Path])
get zst m = maybe (fail "lensStore: invalid ZST") return (I.lookup zst m)

pathStackToLens :: [Path] -> LensH Core Core
pathStackToLens = pathL . concat . reverse

-- not sure about this interface
-- hermitKernel :: (Kernel -> AST -> IO ()) -> ModGuts -> CoreM ModGuts
-- hermitKernel (lensStore f) where f :: LensStore -> ZST -> IO ()
-- hermitKernel $ lensStore $ \ lenstore zst -> do ...
lensStore :: (LensStore -> ZST -> IO ()) -> Kernel -> AST -> IO ()
lensStore callback kernel initAST = do
    store <- newTMVarIO $ I.fromList [(0,(initAST, [[]]))]
    key <- newTMVarIO (1::Int)

    let newKey = do
            k <- takeTMVar key
            putTMVar key (k+1)
            return k

        ls = LensStore
            { resumeL = \ (ZST zst) -> do
                            m <- atomically $ readTMVar store
                            (ast,_) <- get zst m
                            resumeK kernel ast
            , abortL = abortK kernel
            , applyL = \ (ZST zst) rr -> do
                            m <- atomically $ takeTMVar store
                            (ast, ps) <- get zst m
                            ast' <- applyK kernel ast (focusR (pathStackToLens ps) rr)
                            atomically $ do
                                            k <- newKey
                                            putTMVar store $ I.insert k (ast', ps) m
                                            return (ZST k)
            , queryL = \ (ZST zst) t -> do
                                        m <- atomically $ readTMVar store
                                        (ast, ps) <- get zst m
                                        queryK kernel ast (focusT (pathStackToLens ps) t)
            , deleteL = \ (ZST zst) -> atomically $ do
                                        m <- takeTMVar store
                                        putTMVar store $ I.delete zst m
            , listL = do m <- atomically $ readTMVar store
                         return [ ZST zst | zst <- I.keys m ]
            , modPathL = \ (ZST zst) f -> do
                                        m <- atomically $ takeTMVar store
                                        (ast, p:ps) <- get zst m
                                        let p' = f p
                                        if p == p'
                                        then atomically $ putTMVar store m
                                        else do condM (queryK kernel ast (testLensT (pathStackToLens (p':ps))))
                                                      (atomically $ putTMVar store $ I.insert zst (ast, p':ps) m)
                                                      (atomically $ putTMVar store m) -- throw error too?
            , scopeStartL = \ (ZST zst) -> atomically $ do
                                        m <- takeTMVar store
                                        (ast, ps) <- get zst m
                                        putTMVar store $ I.insert zst (ast, []:ps) m
            , scopeEndL = \ (ZST zst) -> atomically $ do
                                        m <- takeTMVar store
                                        (ast, _:ps) <- get zst m
                                        case ps of
                                            [] -> fail "lensStore: no scope to end"
                                            _  -> putTMVar store $ I.insert zst (ast, ps) m
            }

    callback ls $ ZST 0
