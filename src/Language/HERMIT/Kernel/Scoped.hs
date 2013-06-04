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
import Control.Exception (bracketOnError, catch, SomeException)

import qualified Data.IntMap as I

import GhcPlugins hiding (Direction,L)

import Language.HERMIT.Core
import Language.HERMIT.Kure
import Language.HERMIT.Monad
import Language.HERMIT.Kernel

----------------------------------------------------------------------------

-- | A primitive means of denoting navigation of a tree (within a local scope).
data Direction = L -- ^ Left
               | R -- ^ Right
               | U -- ^ Up
               | D -- ^ Down
               | T -- ^ Top
               deriving (Eq,Show)

-- | The path within the current local scope.
newtype LocalPath a = LocalPath [a] deriving Eq

type LocalPathH = LocalPath Int

instance Show a => Show (LocalPath a) where
  show (LocalPath p) = show (reverse p)

-- | An empty 'LocalPath'.
emptyLocalPath :: LocalPath a
emptyLocalPath = LocalPath []

-- | Convert between path representations.
localPath2Path :: LocalPath a -> Path a
localPath2Path (LocalPath p) = reverse p

localPaths2Paths :: [LocalPath a] -> [Path a]
localPaths2Paths = reverse . map localPath2Path

-- | Movement confined within the local scope.
moveLocally :: Direction -> LocalPathH -> LocalPathH
moveLocally D (LocalPath ns)             = LocalPath (0:ns)
moveLocally U (LocalPath (_:ns))         = LocalPath ns
moveLocally L (LocalPath (n:ns)) | n > 0 = LocalPath ((n-1):ns)
moveLocally R (LocalPath (n:ns))         = LocalPath ((n+1):ns)
moveLocally T _                          = LocalPath []
moveLocally _ p                          = p

-- | Add a 'Path' to the end of a 'LocalPath'.
extendLocalPath :: Path a -> LocalPath a -> LocalPath a
extendLocalPath p (LocalPath lp) = LocalPath (reverse p ++ lp)

pathStackToLens :: [LocalPathH] -> LocalPathH -> LensH ModGuts Core
pathStackToLens ps p = injectL >>> pathL (concat $ localPaths2Paths (p:ps))

----------------------------------------------------------------------------

-- | An alternative HERMIT kernel, that provides scoping.
data ScopedKernel = ScopedKernel
        { resumeS     ::            SAST                                              -> IO (KureM ())
        , abortS      ::                                                                 IO ()
        , applyS      ::            SAST -> RewriteH Core             -> HermitMEnv   -> IO (KureM SAST)
        , queryS      :: forall a . SAST -> TranslateH Core a         -> HermitMEnv   -> IO (KureM a)
        , deleteS     ::            SAST                                              -> IO (KureM ())
        , listS       ::                                                                 IO [SAST]
        , pathS       ::            SAST                                              -> IO (KureM [PathH])
        , modPathS    ::            SAST -> (LocalPathH -> LocalPathH)  -> HermitMEnv -> IO (KureM SAST)
        , beginScopeS ::            SAST                                              -> IO (KureM SAST)
        , endScopeS   ::            SAST                                              -> IO (KureM SAST)
        -- means of accessing the underlying kernel, obviously for unsafe purposes
        , kernelS     ::                                                                 Kernel
        , toASTS      ::            SAST                                              -> IO (KureM AST)
        }

-- | A /handle/ for an 'AST' combined with scoping information.
newtype SAST = SAST Int deriving (Eq, Ord, Show)

-- path stack, representing the base path, then the relative path
type SASTStore = I.IntMap (AST, [LocalPathH], LocalPathH)

get :: Monad m => Int -> SASTStore -> m (AST, [LocalPathH], LocalPathH)
get sAst m = maybe (fail "scopedKernel: invalid SAST") return (I.lookup sAst m)

-- | Ensures that the TMVar is replaced when an error is thrown, and all exceptions are lifted into KureM failures.
safeTakeTMVar :: TMVar a -> (a -> IO b) -> IO (KureM b)
safeTakeTMVar mvar = catchFails . bracketOnError (atomically $ takeTMVar mvar) (atomically . putTMVar mvar)

-- | Lifts exceptions into KureM failures.
catchFails :: IO a -> IO (KureM a)
catchFails io = (io >>= (return.return)) `catch` (\e -> return $ fail $ show (e :: SomeException))

-- | Start a HERMIT client by providing an IO function that takes the initial 'ScopedKernel' and inital 'SAST' handle.
--   The 'Modguts' to 'CoreM' Modguts' function required by GHC Plugins is returned.
scopedKernel :: (ScopedKernel -> SAST -> IO ()) -> ModGuts -> CoreM ModGuts
scopedKernel callback = hermitKernel $ \ kernel initAST -> do
    store <- newTMVarIO $ I.fromList [(0,(initAST, [], emptyLocalPath))]
    key <- newTMVarIO (1::Int)

    let newKey = do
            k <- takeTMVar key
            putTMVar key (k+1)
            return k

        skernel = ScopedKernel
            { resumeS     = \ (SAST sAst) -> catchFails $ do
                                m <- atomically $ readTMVar store
                                (ast,_,_) <- get sAst m
                                resumeK kernel ast
            , abortS      = abortK kernel
            , applyS      = \ (SAST sAst) rr env -> safeTakeTMVar store $ \ m -> do
                                (ast, base, rel) <- get sAst m
                                applyK kernel ast (focusR (pathStackToLens base rel) rr) env
                                  >>= runKureM (\ ast' -> atomically $ do k <- newKey
                                                                          putTMVar store $ I.insert k (ast', base, rel) m
                                                                          return $ SAST k)
                                               fail
            , queryS      = \ (SAST sAst) t env -> catchFails $ do
                                m <- atomically $ readTMVar store
                                (ast, base, rel) <- get sAst m
                                queryK kernel ast (focusT (pathStackToLens base rel) t) env
                                    >>= runKureM return fail
            , deleteS     = \ (SAST sAst) -> safeTakeTMVar store $ \ m -> do
                                (ast,_,_) <- get sAst m
                                let m' = I.delete sAst m
                                    fst3 (x,_,_) = x
                                    asts = I.foldr ((:) . fst3) [] m'
                                if ast `elem` asts
                                    then return ()
                                    else deleteK kernel ast
                                atomically $ putTMVar store m'
            , listS       = do m <- atomically $ readTMVar store
                               return [ SAST sAst | sAst <- I.keys m ]
            , pathS       = \ (SAST sAst) -> catchFails $ do
                                m <- atomically $ readTMVar store
                                (_, base, rel) <- get sAst m
                                return $ localPaths2Paths (rel : base)
            , modPathS    = \ (SAST sAst) f env -> safeTakeTMVar store $ \ m -> do
                                (ast, base, rel) <- get sAst m
                                let rel' = f rel
                                queryK kernel ast (testLensT (pathStackToLens base rel')) env
                                  >>= runKureM (\ b -> if rel == rel'
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
                                                putTMVar store $ I.insert k (ast, rel : base, emptyLocalPath) m
                                                return $ SAST k
            , endScopeS   = \ (SAST sAst) -> safeTakeTMVar store $ \m -> do
                                (ast, base, _) <- get sAst m
                                case base of
                                    []          -> fail "Scoped Kernel: no scope to end."
                                    rel : base' -> atomically $ do k <- newKey
                                                                   putTMVar store $ I.insert k (ast, base', rel) m
                                                                   return $ SAST k
            , kernelS     = kernel
            , toASTS      = \ (SAST sAst) -> catchFails $ do
                                m <- atomically $ readTMVar store
                                (ast, _, _) <- get sAst m
                                return ast
            }

    callback skernel $ SAST 0
