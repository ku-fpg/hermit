{-# LANGUAGE RankNTypes, FlexibleContexts #-}
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

import Data.Maybe (fromMaybe)
import Data.Monoid (mempty)
import qualified Data.IntMap as I

import GhcPlugins hiding (Direction,L)

import Language.HERMIT.Core
import Language.HERMIT.Context
import Language.HERMIT.Kure
import Language.HERMIT.Monad
import Language.HERMIT.Kernel

----------------------------------------------------------------------------

-- | A primitive means of denoting navigation of a tree (within a local scope).
data Direction = L -- ^ Left
               | R -- ^ Right
               | U -- ^ Up
               | T -- ^ Top
               deriving (Eq,Show)

-- | The path within the current local scope.
type LocalPath = SnocPath
type LocalPathH = LocalPath Crumb

pathStack2Paths :: [LocalPath crumb] -> LocalPath crumb -> [Path crumb]
pathStack2Paths ps p = reverse (map snocPathToPath (p:ps))

-- | Add a 'Path' to the end of a 'LocalPath'.
extendLocalPath :: Path crumb -> LocalPath crumb -> LocalPath crumb
extendLocalPath p (SnocPath sp) = SnocPath (reverse p ++ sp)
{-# INLINE extendLocalPath #-}

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
testPathStackT :: [LocalPathH] -> LocalPathH -> TranslateH ModGuts Bool
testPathStackT ps p = testLensT (pathStackToLens ps p :: LensH ModGuts CoreTC)

----------------------------------------------------------------------------

-- | An alternative HERMIT kernel, that provides scoping.
data ScopedKernel = ScopedKernel
  { resumeS      ::            SAST                                              -> IO (KureM ())
  , abortS       ::                                                                 IO ()
  , applyS       :: forall g. (Injection ModGuts g, Walker HermitC g) =>
                               SAST -> RewriteH g                  -> HermitMEnv -> IO (KureM SAST)
  , queryS       :: forall a g . (Injection ModGuts g, Walker HermitC g) =>
                               SAST -> TranslateH g a              -> HermitMEnv -> IO (KureM a)
  , deleteS      ::            SAST                                              -> IO (KureM ())
  , listS        ::                                                                 IO [SAST]
  , pathS        ::            SAST                                              -> IO (KureM [PathH])
  , modPathS     ::            SAST -> (LocalPathH -> LocalPathH)  -> HermitMEnv -> IO (KureM SAST)
  , beginScopeS  ::            SAST                                              -> IO (KureM SAST)
  , endScopeS    ::            SAST                                              -> IO (KureM SAST)
  -- means of accessing the underlying kernel, obviously for unsafe purposes
  , kernelS      ::                                                                 Kernel
  , toASTS       ::            SAST                                              -> IO (KureM AST)
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
    store <- newTMVarIO $ I.fromList [(0,(initAST, [], mempty))]
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
                                return $ pathStack2Paths base rel
            , modPathS    = \ (SAST sAst) f env -> safeTakeTMVar store $ \ m -> do
                                (ast, base, rel) <- get sAst m
                                let rel' = f rel
                                queryK kernel ast (testPathStackT base rel') env
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
            , toASTS      = \ (SAST sAst) -> catchFails $ do
                                m <- atomically $ readTMVar store
                                (ast, _, _) <- get sAst m
                                return ast
            }

    callback skernel $ SAST 0
