{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
module HERMIT.Shell.Completion (completer) where

import Control.Applicative
import Control.Arrow
import Control.Monad.State

import Data.Dynamic
import Data.List (isPrefixOf, nub)
import qualified Data.Map as M
import Data.Maybe (fromMaybe)

import HERMIT.Kure
import HERMIT.External
import qualified HERMIT.GHC as GHC
import HERMIT.Kernel
import HERMIT.Parser

import HERMIT.Dictionary.Inline
import HERMIT.Dictionary.Navigation
import HERMIT.Dictionary.Reasoning
import HERMIT.Dictionary.Rules

import HERMIT.Shell.Interpreter
import HERMIT.Shell.Proof
import HERMIT.Shell.Types

import System.Console.Haskeline hiding (catch, display)

----------------------------------------------------------------------------------

completer :: (MonadCatch m, CLMonad m) => String -> String -> m [Completion]
completer rPrev so_far = do
    (ps,ast) <- gets (cl_proofstack &&& cl_cursor)
    case M.lookup ast ps of
        Just (_:_)  -> withProofExternals $ shellComplete rPrev so_far
        _           -> shellComplete rPrev so_far

shellComplete :: (MonadCatch m, CLMonad m) => String -> String -> m [Completion]
shellComplete rPrev so_far = do
    let (partial, _) = toUnmatched rPrev
    if null partial
    then completionsFor so_far [CommandC]
    else case parseExprH partial of
            Left _   -> return []
            Right e  -> do
                eds <- attemptM $ exprToDyns e
                case eds of
                    Left msg -> liftIO $ putStrLn ("\n" ++ msg) >> return []
                    Right ds -> do
                        let ts = [ head args | d <- ds
                                             , let args = fst (splitFunTyArgs (dynTypeRep d))
                                             , not (null args) ]
                        completionsFor so_far $ filterUnknowns $ map (completionType.show) ts

completionsFor :: (MonadCatch m, CLMonad m)
               => String -> [CompletionType] -> m [Completion]
completionsFor so_far cts = do
    qs <- mapM completionQuery cts
    (k,(env,ast)) <- gets (cl_kernel &&& cl_kernel_env &&& cl_cursor)
    -- 'liftM snd' is because we assume completion queries don't create new ASTs
    cls <- forM qs $ \ q -> catchM (do q' <- addFocusT q ; liftM snd $ queryK k q' Never env ast) (\_ -> return [])
    return $ map simpleCompletion $ nub $ filter (so_far `isPrefixOf`) $ concat cls

data CompletionType = ConsiderC       -- considerable constructs
                    | BindingOfC      -- bindingOfT
                    | BindingGroupOfC -- bindingGroupOfT
                    | RhsOfC          -- rhsOfT
                    | OccurrenceOfC   -- occurrenceOfT
                    | InlineC         -- complete with names that can be inlined
                    | InScopeC        -- complete with in-scope variable names
                    | LemmaC          -- complete with list of lemmas
                    | CommandC        -- complete using dictionary commands (default)
                    | CoreC           -- complete with opening Core fragment bracket [|
                    | NothingC        -- no completion
                    | RuleC           -- complete with GHC rewrite rule name
                    | StringC         -- complete with open quotes
                    | UnknownC String -- unknown Extern instance (empty completion)

completionType :: String -> CompletionType
completionType s = fromMaybe (UnknownC s) (lookup s m)
    where m = [ ("BindingName"   , BindingOfC)
              , ("Considerable"  , ConsiderC)
              , ("CoreBox"       , CoreC)
              , ("HermitName"    , NothingC)
              , ("IntBox"        , NothingC)
              , ("LemmaName"     , LemmaC)
              , ("OccurrenceName", OccurrenceOfC)
              , ("RewriteCoreBox", CommandC) -- be more specific than CommandC?
              , ("RhsOfName"     , RhsOfC)
              , ("RuleName"      , RuleC)
              , ("StringBox"     , StringC)
              ]

filterUnknowns :: [CompletionType] -> [CompletionType]
filterUnknowns l = if null l' then l else l'
    where l' = filter (\case UnknownC _ -> False ; _ -> True) l

completionQuery :: (MonadIO m, MonadState CommandLineState m) => CompletionType -> m (TransformH CoreTC [String])
completionQuery ConsiderC       = return $ pure $ map fst considerables
completionQuery OccurrenceOfC   = return $ occurrenceOfTargetsT    >>^ GHC.varSetToStrings >>^ map ('\'':)
completionQuery BindingOfC      = return $ bindingOfTargetsT       >>^ GHC.varSetToStrings >>^ map ('\'':)
completionQuery BindingGroupOfC = return $ bindingGroupOfTargetsT  >>^ GHC.varSetToStrings >>^ map ('\'':)
completionQuery RhsOfC          = return $ rhsOfTargetsT           >>^ GHC.varSetToStrings >>^ map ('\'':)
completionQuery InlineC         = return $ promoteT inlineTargetsT >>^                         map ('\'':)
completionQuery InScopeC        = return $ pure ["'"] -- TODO
completionQuery LemmaC          = do
    let findTemps [] = []
        findTemps (pt@(Unproven {}) : _) = map (show . fst) (ptAssumed pt)
        findTemps (_ : r) = findTemps r
    cur <- gets cl_cursor
    tempLemmas <- gets (findTemps . fromMaybe [] . M.lookup cur . cl_proofstack)
    return $ liftM ((tempLemmas ++) . map show . M.keys) $ getLemmasT
completionQuery NothingC        = return $ pure []
completionQuery RuleC           = return $ liftM (map (show . fst)) $ getHermitRulesT
completionQuery StringC         = return $ pure ["\""]
completionQuery CommandC        = gets cl_externals >>= return . pure . map externName
completionQuery CoreC           = return $ pure ["[|"]
-- Need to modify opts in completionType function to add this type.
completionQuery (UnknownC s)    = do
    liftIO $ putStrLn $ "\nCannot tab complete: unknown argument type: " ++ s
    return (pure [])

-- | Take a reversed string, find substring back to first unmatched open paren (or the end).
-- Returns that substring (unreversed), and remaining (reversed) string.
--
-- ex 1. toUnmatched "zab rab( oof"        ==> ("bar baz"       , "( oof")
-- ex 2. toUnmatched ")xuuq zab( rab( oof" ==> ("bar (baz quux)", "( oof")
toUnmatched :: String -> (String, String)
toUnmatched = go 0 ""
    where go :: Int -> String -> String -> (String, String)
          go n acc s@('(':cs)
            | n > 0         = go (n-1) ('(':acc) cs
            | otherwise     = (acc, s)
          go n acc (')':cs) = go (n+1) (')':acc) cs
          go n acc (c:cs)   = go n     (c:acc)   cs
          go _ acc []       = (acc, [])

