{-# LANGUAGE PatternGuards, DataKinds, ScopedTypeVariables, DeriveDataTypeable,
             OverloadedStrings, KindSignatures, GADTs, TypeFamilies #-}

module Language.HERMIT.Plugin.Restful (passes) where

import Control.Applicative
import Control.Arrow
import Control.Concurrent.STM
import Control.Monad
import Control.Monad.IO.Class (liftIO)

import Data.Default
import Data.Dynamic
import qualified Data.Map as M
import Data.Monoid ((<>))
import qualified Data.Text.Lazy as T

-- The Prelude version of catch has been deprecated.
import Prelude hiding (catch)
import Control.Exception hiding (catch)

import Language.HERMIT.External
import Language.HERMIT.HermitEnv
import Language.HERMIT.HermitExpr
import Language.HERMIT.HermitKure
import Language.HERMIT.Dictionary
import Language.HERMIT.Kernel
import Language.HERMIT.PrettyPrinter.AST (corePrettyH)
import Language.HERMIT.Interp

import Language.HERMIT.Plugin.Common

import Language.KURE

import qualified Text.PrettyPrint.MarkedHughesPJ as PP
import Web.Scotty as S

passes :: [NamedPass]
passes = [("w", restful)]

restful :: HermitPass
restful opts modGuts = hermitKernel (webapp dict) modGuts
    where dict = dictionary [] modGuts

webapp :: M.Map String [Dynamic] -> Kernel -> AST -> IO ()
webapp dict kernel _initAst = do
    state <- newTMVarIO $ RestfulState idL

    let respondWithFocus :: AST -> ActionM ()
        respondWithFocus ast = do
            r <- withState $ \ s -> queryK kernel ast (focusT (r_lens s) ppJSON)
            html $ "<pre>" <> T.pack r <> "</pre>"

        withState :: (RestfulState -> IO a) -> ActionM a
        withState act = liftIO $ atomically (readTMVar state) >>= act

        modifyState :: (RestfulState -> IO (a,RestfulState)) -> ActionM a
        modifyState act = liftIO $ do
            (r,s') <- atomically (takeTMVar state) >>= act
            atomically $ putTMVar state s'
            return r

    scotty 3000 $ do
        get "/" $ redirect "/list"
        get "/list" $ do
            l <- liftIO $ listK kernel
            json $ map show l -- todo: not show!

        get "/:ast" $ do
            ast <- param "ast"
            respondWithFocus $ AST ast

        delete "/:ast" $ do
            ast <- param "ast"
            liftIO $ deleteK kernel $ AST ast
            redirect "/list"

        get "/:ast/query/:q" $ do
            ast <- param "ast"
            Query q <- parseCommand dict =<< param "q" -- todo parse this from json?
            res <- withState $ \s -> (liftM Right $ queryK kernel (AST ast) (focusT (r_lens s) q)) `catch` (return . Left)
            either (raise . T.pack) (S.text . T.pack . show) res

        get "/:ast/apply/:rr" $ do
            ast <- param "ast"
            Apply rr <- parseCommand dict =<< param "rr" -- todo parse this from json?
            ast' <- withState $ \s -> (liftM Right $ applyK kernel (AST ast) (focusR (r_lens s) rr))
                                      `catch` (return . Left)
            either (raise . T.pack) respondWithFocus ast' -- todo: return ast'

        -- todo: do we really need the ast here?
        get "/:ast/quit" $ do
            ast <- param "ast"
            -- take the ast and leave it empty, so any further requests are rejected
            liftIO $ quitK kernel (AST ast)
            S.text "quitting..."

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

{-
                let new_lens = case (, c_path) of
                        (R, kid : rest)            -> pathL $ reverse ((kid + 1) : rest)
                        (L, kid : rest)  | kid > 0 -> pathL $ reverse ((kid - 1) : rest)
                        _               -> r_lens s
-}


-- todo: move to pretty printer modules
ppJSON :: TranslateH Core String -- todo: change
ppJSON = corePrettyH def >>= pure . PP.render

-- rather than abuse the command line parser here,
-- need to assign each command a unique id, and call with those
parseCommand :: M.Map String [Dynamic] -> String -> ActionM KernelCommand
parseCommand dict s = either (raise . T.pack) return $ do
    expr <- parseExprH s
    interpExprH dict interpKernelCommand expr

catch :: IO a -> (String -> IO a) -> IO a
catch = catchJust (\ (err :: IOException) -> return (show err))

data RestfulState = RestfulState
        { r_lens   :: LensH Core Core    -- ^ stack of lenses
        }

{- not sure if it makes sense to have these and a dictionary
data RestfulCommand :: * where
   Status        ::                             RestfulCommand
--   Message       :: String                   -> RestfulCommand
--   PushFocus     :: LensH Core Core          -> RestfulCommand
   Root          ::                             RestfulCommand
   SetPretty     :: String                   -> RestfulCommand
   KernelCommand :: KernelCommand            -> RestfulCommand
   Child         :: Int                      -> RestfulCommand

data RestfulCommandBox = RestfulCommandBox RestfulCommand deriving Typeable

instance Extern RestfulCommand where
    type Box RestfulCommand = RestfulCommandBox
    box i = RestfulCommandBox i
    unbox (RestfulCommandBox i) = i

interpRestfulCommand :: [Interp RestfulCommand]
interpRestfulCommand =
    [ Interp $ \ (RestfulCommandBox cmd)     -> cmd
    , Interp $ \ (LensCoreCoreBox l)         -> PushFocus l
    , Interp $ \ (IntBox i)                  -> PushFocus $ childL i
    , Interp $ \ (StringBox str)             -> Message str
    ]
-}

{-
      kernelAct st (Query q) = do

              (query (cl_cursor st) (focusT (cl_lens st) q) >>= print)
                `catch` \ msg -> putStrLn $ "Error thrown: " ++ msg
              loop st

      kernelAct st (Apply rr) = do
              st2 <- (do ast' <- applyK kernel (cl_cursor st) (focusR (cl_lens st) rr)
                         let st' = st { cl_cursor = ast' }
                         showFocus st'
                         return st') `catch` \  msg -> do
                                        putStrLn $ "Error thrown: " ++ msg
                                        return st
              loop st2

-}

