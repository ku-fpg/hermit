{-# LANGUAGE RankNTypes #-}
module Language.HERMIT.Kernel.Scoped
       (
         Direction(..)
       , LocalPath
       , moveLocally
       , extendLocalPath
       , ScopedKernel(..)
       , SAST(..)
       , scopedKernel
) where

import Control.Arrow
import Control.Concurrent.STM
import Control.Exception.Base (bracketOnError)

import qualified Data.IntMap as I

import GhcPlugins hiding (Direction,L)

import Language.HERMIT.Kure
import Language.HERMIT.Kernel
import Language.HERMIT.Monad

----------------------------------------------------------------------------

-- | A primitive means of denoting navigation of a tree (within a local scope).
data Direction = L -- ^ Left
               | R -- ^ Right
               | U -- ^ Up
               | D -- ^ Down
               | T -- ^ Top
               deriving (Eq,Show)

-- | The path within the current local scope.
newtype LocalPath = LocalPath [Int] deriving Eq

instance Show LocalPath where
  show (LocalPath p) = show (reverse p)

-- | An empty 'LocalPath'.
emptyLocalPath :: LocalPath
emptyLocalPath = LocalPath []

-- | Convert between path representations.
localPath2Path :: LocalPath -> Path
localPath2Path (LocalPath p) = reverse p

-- Convert between path representations.
-- path2LocalPath :: Path -> LocalPath
-- path2LocalPath p = LocalPath (reverse p)

localPaths2Paths :: [LocalPath] -> [Path]
localPaths2Paths = reverse . map localPath2Path

-- | Movement confined within the local scope.
moveLocally :: Direction -> LocalPath -> LocalPath
moveLocally D (LocalPath ns)             = LocalPath (0:ns)
moveLocally U (LocalPath (_:ns))         = LocalPath ns
moveLocally L (LocalPath (n:ns)) | n > 0 = LocalPath ((n-1):ns)
moveLocally R (LocalPath (n:ns))         = LocalPath ((n+1):ns)
moveLocally T _                          = LocalPath []
moveLocally _ p                          = p

-- | Add a 'Path' to the end of a 'LocalPath'.
extendLocalPath :: Path -> LocalPath -> LocalPath
extendLocalPath p (LocalPath lp) = LocalPath (reverse p ++ lp)

pathStackToLens :: [LocalPath] -> LocalPath -> LensH ModGuts Core
pathStackToLens ps p = injectL >>> pathL (concat $ localPaths2Paths (p:ps))

----------------------------------------------------------------------------

-- | An alternative HERMIT kernel, that provides scoping.
data ScopedKernel = ScopedKernel
        { resumeS     ::            SAST                                              -> IO ()
        , abortS      ::                                                                 IO ()
        , applyS      ::            SAST -> RewriteH Core             -> HermitMEnv   -> IO (KureMonad SAST)
        , queryS      :: forall a . SAST -> TranslateH Core a         -> HermitMEnv   -> IO (KureMonad a)
        , deleteS     ::            SAST                                              -> IO ()
        , listS       ::                                                                 IO [SAST]
        , pathS       ::            SAST                                              -> IO [Path]
        , modPathS    ::            SAST -> (LocalPath -> LocalPath)  -> HermitMEnv   -> IO (KureMonad SAST)
        , beginScopeS ::            SAST                                              -> IO SAST
        , endScopeS   ::            SAST                                              -> IO SAST
        }

-- | A /handle/ for an 'AST' combined with scoping information.
newtype SAST = SAST Int deriving (Eq, Ord, Show)

-- path stack, representing the base path, then the relative path
type SASTStore = I.IntMap (AST, [LocalPath], LocalPath)

get :: Monad m => Int -> SASTStore -> m (AST, [LocalPath], LocalPath)
get sAst m = maybe (fail "scopedKernel: invalid SAST") return (I.lookup sAst m)

safeTakeTMVar :: TMVar a -> (a -> IO b) -> IO b
safeTakeTMVar mvar = bracketOnError (atomically $ takeTMVar mvar) (atomically . putTMVar mvar)

-- | Start a HERMIT client by providing an IO function that takes the initial 'ScopedKernel' and inital 'SAST' handle.
--   The 'Modguts' to 'CoreM' Modguts' function required by GHC Plugins is returned.
scopedKernel :: (ScopedKernel -> SAST -> IO ()) -> ModGuts -> CoreM ModGuts
scopedKernel callback = hermitKernel $ \ kernel initAST -> do
    store <- newTMVarIO $ I.fromList [(0,(initAST, [], emptyLocalPath))]
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
            , applyS      = \ (SAST sAst) rr env -> safeTakeTMVar store $ \ m -> do
                                (ast, base, rel) <- get sAst m
                                applyK kernel ast (focusR (pathStackToLens base rel) rr) env
                                  >>= runKureMonad (\ ast' -> atomically $ do k <- newKey
                                                                              putTMVar store $ I.insert k (ast', base, rel) m
                                                                              return $ return $ SAST k)
                                                   (failCleanup m)
            , queryS      = \ (SAST sAst) t env -> do
                                m <- atomically $ readTMVar store
                                (ast, base, rel) <- get sAst m
                                queryK kernel ast (focusT (pathStackToLens base rel) t) env
            , deleteS     = \ (SAST sAst) -> atomically $ do
                                m <- takeTMVar store
                                putTMVar store $ I.delete sAst m
            , listS       = do m <- atomically $ readTMVar store
                               return [ SAST sAst | sAst <- I.keys m ]
            , pathS       = \ (SAST sAst) -> atomically $ do
                                m <- readTMVar store
                                (_, base, rel) <- get sAst m
                                return $ localPaths2Paths (rel : base)
            , modPathS    = \ (SAST sAst) f env -> safeTakeTMVar store $ \ m -> do
                                (ast, base, rel) <- get sAst m
                                let rel' = f rel
                                queryK kernel ast (testLensT (pathStackToLens base rel')) env
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
                                putTMVar store $ I.insert k (ast, rel : base, emptyLocalPath) m
                                return $ SAST k
            , endScopeS   = \ (SAST sAst) -> atomically $ do
                                m <- takeTMVar store
                                (ast, base, _) <- get sAst m
                                case base of
                                    []          -> fail "Scoped Kernel: no scope to end."
                                    rel : base' -> do k <- newKey
                                                      putTMVar store $ I.insert k (ast, base', rel) m
                                                      return $ SAST k
            }

    callback skernel $ SAST 0
