{-# LANGUAGE PatternGuards, DataKinds, ScopedTypeVariables, DeriveDataTypeable,
             OverloadedStrings, KindSignatures, GADTs, TypeFamilies #-}

module Language.HERMIT.Plugin.Restful (passes) where

import Control.Applicative
import Control.Arrow
import Control.Concurrent.STM
import Control.Monad
import Control.Monad.IO.Class (liftIO)

import Data.Aeson
import Data.Default
import Data.Dynamic
import Data.List hiding (delete)
import qualified Data.Map as M
import Data.Monoid ((<>))
import qualified Data.Text.Lazy as T

-- The Prelude version of catch has been deprecated.
import Prelude hiding (catch)
import Control.Exception hiding (catch)

import Language.HERMIT.Dictionary
import Language.HERMIT.External
import Language.HERMIT.HermitEnv
import Language.HERMIT.HermitExpr
import Language.HERMIT.HermitKure
import Language.HERMIT.Interp
import Language.HERMIT.Kernel
import Language.HERMIT.Plugin.Common
import Language.HERMIT.PrettyPrinter.JSON

import Language.KURE

import Paths_hermit

import Web.Scotty as S

import Debug.Trace

passes :: [NamedPass]
passes = [("w", restful)]

restful :: HermitPass
restful opts modGuts = hermitKernel (webapp dict indexfile) modGuts
    where dict = dictionary [] modGuts
          indexfile = head [ o | o <- opts, ".html" `isSuffixOf` o ]

-- todo: get rid of state, each command from client should supply focus
data RestfulState = RestfulState
        { r_lens   :: LensH Core Core    -- ^ stack of lenses
        }

webapp :: M.Map String [Dynamic] -> FilePath -> Kernel -> AST -> IO ()
webapp dict indexfile kernel _initAst = do
    state <- newTMVarIO $ RestfulState idL

    dataDir <- getDataDir

    let respondWithFocus :: AST -> ActionM ()
        respondWithFocus ast@(AST i) = do
            val <- withState $ \ s -> queryK kernel ast (focusT (r_lens s) (corePrettyH def))
            S.json $ object ["ast" .= i, "code" .= val]

        withState :: (RestfulState -> IO a) -> ActionM a
        withState act = liftIO $ atomically (readTMVar state) >>= act

        modifyState :: (RestfulState -> IO (a,RestfulState)) -> ActionM a
        modifyState act = liftIO $ do
            (r,s') <- atomically (takeTMVar state) >>= act
            atomically $ putTMVar state s'
            return r

    scotty 3000 $ do
        get "/" $ file indexfile
        get "/jquery.js" $ file $ dataDir ++ "/javascript/jquery.js"
        get "/jquery-json.js" $ file $ dataDir ++ "/javascript/jquery-json.js"

        get "/list" $ do
            l <- liftIO $ listK kernel
            S.json [ i | AST i <- l ]

        get "/:ast" $ do
            ast <- param "ast"
            respondWithFocus $ AST ast

        delete "/:ast" $ do
            ast <- param "ast"
            liftIO $ deleteK kernel $ AST ast
            redirect "/list"

        post "/:ast/query" $ do
            ast <- param "ast"
            Query q <- parseCommand dict =<< jsonData
            res <- withState $ \s -> (liftM Right $ queryK kernel (AST ast) (focusT (r_lens s) q)) `catch` (return . Left)
            either (raise . T.pack) (S.text . T.pack . show) res

        post "/:ast/apply" $ do
            ast <- param "ast"
            Apply rr <- parseCommand dict =<< jsonData
            ast' <- withState $ \s -> (liftM Right $ applyK kernel (AST ast) (focusR (r_lens s) rr))
                                      `catch` (return . Left)
            either (raise . T.pack) respondWithFocus ast'

        -- todo: do we really need the ast here?
        post "/:ast/quit" $ do
            ast <- param "ast"
            liftIO $ quitK kernel (AST ast)
            S.text "quitting..."

        -- todo: child/parent belongs in a higher-level API
        get "/:ast/child/:i" $ do
            ast <- param "ast"
            i <- param "i"
            unless (i >= 0) $ raise "child cannot be negative"

            kids <- withState $ \s -> queryK kernel (AST ast) (focusT (r_lens s) (arr numChildren))
            unless (i < kids) $ raise $ "only " <> T.pack (show kids) <> " children"

            modifyState $ \s -> do
                ContextPath c_path <- queryK kernel (AST ast) (focusT (r_lens s) pathT)
                let new_lens = pathL $ reverse (i : c_path)
                condM (queryK kernel (AST ast) (testM new_lens))
                      (return ((),s { r_lens = new_lens }))
                      (return ((),s                      ))
            respondWithFocus $ AST ast

        get "/:ast/parent" $ do
            ast <- param "ast"
            modifyState $ \s -> do
                ContextPath c_path <- queryK kernel (AST ast) (focusT (r_lens s) pathT)
                case c_path of
                    [] -> return ((), s)
                    (_:rest) -> do let new_lens = pathL $ reverse rest
                                   condM (queryK kernel (AST ast) (testM new_lens))
                                         (return ((),s { r_lens = new_lens }))
                                         (return ((),s                      ))
            respondWithFocus $ AST ast

-- rather than abuse the command line parser here,
-- need to assign each command a unique id, and call with those
parseCommand :: M.Map String [Dynamic] -> ExprH -> ActionM KernelCommand
parseCommand dict expr = either (raise . T.pack) return $ interpExprH dict interpKernelCommand expr

instance FromJSON ExprH where
   parseJSON (Object o) = do
        con :: String <- o .: "type"
        case con of
            "Src" -> SrcName <$> o .: "value"
            "Cmd" -> CmdName <$> o .: "value"
            "Str" -> StrName <$> o .: "value"
            "App" -> AppH <$> o .: "lhs" <*> o .: "rhs"

   parseJSON _ = mzero

catch :: IO a -> (String -> IO a) -> IO a
catch = catchJust (\ (err :: IOException) -> return (show err))

{-
data RestfulCommand :: * where
    WithFocus     :: LensH Core Core -> KernelCommand -> RestfulCommand
    KernelCommand :: KernelCommand            -> RestfulCommand
{- not sure if it makes sense to have these and a dictionary
    Status        ::                             RestfulCommand
--  Message       :: String                   -> RestfulCommand
--  PushFocus     :: LensH Core Core          -> RestfulCommand
    Root          ::                             RestfulCommand
    SetPretty     :: String                   -> RestfulCommand
    Child         :: Int                      -> RestfulCommand
-}


data RestfulCommandBox = RestfulCommandBox RestfulCommand deriving Typeable

instance Extern RestfulCommand where
    type Box RestfulCommand = RestfulCommandBox
    box i = RestfulCommandBox i
    unbox (RestfulCommandBox i) = i

interpRestfulCommand :: [Interp RestfulCommand]
interpRestfulCommand =
    [ Interp $ \ (RestfulCommandBox cmd)     -> cmd
    , Interp $ \ (LensCoreCoreBox l) (KernelCommandBox c) -> WithFocus l c -- no idea if this makes sense
    , Interp $ \ (IntBox i)                  -> WithFocus $ childL i
--    , Interp $ \ (StringBox str)             -> Message str
    ]

restful_externals :: [External]
restful_externals = map (.+ Restful) $
   [  external "focus" WithFocus [ "apply kernel command with focus" ]
   ]
-}
