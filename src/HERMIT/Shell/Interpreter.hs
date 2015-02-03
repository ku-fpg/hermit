{-# LANGUAGE ConstraintKinds, KindSignatures, GADTs, InstanceSigs,
             FlexibleContexts, ScopedTypeVariables #-}

module HERMIT.Shell.Interpreter
    ( -- * The HERMIT Interpreter
      Interp
    , interp
    , interpM
    , interpEM
    , interpExprH
    , exprToDyns
    ) where

import Control.Monad (liftM, liftM2)
import Control.Monad.State (MonadState(get), gets)

import Data.Char
import Data.Dynamic
import qualified Data.Map as M

import HERMIT.External
import HERMIT.Kure
import HERMIT.Monad
import HERMIT.Name
import HERMIT.Parser

import HERMIT.Dictionary.Navigation
import HERMIT.Dictionary.Rules

import HERMIT.Shell.Dictionary
import HERMIT.Shell.Types

-- | An 'Interp' @cmd@ is a /possible/ means of converting a 'Typeable' value to a value of type @cmd@.
data Interp :: (* -> *) -> * -> * where
   Interp :: Typeable b => (b -> ExprH -> m a) -> Interp m a

-- | An 'Interp' with no effects.
interp :: (Monad m, Typeable b) => (b -> a) -> Interp m a
interp f = Interp (const . return . f)

-- | An 'Interp' which can affect the shell.
interpM :: (CLMonad m, Typeable b) => (b -> m a) -> Interp m a
interpM f = Interp (const . f)

-- | Like 'InterpM', but with access to the original expression.
interpEM :: (CLMonad m, Typeable b) => (b -> ExprH -> m a) -> Interp m a
interpEM = Interp

instance Monad m => Functor (Interp m) where
  fmap :: (a -> b) -> Interp m a -> Interp m b
  fmap f (Interp g) = Interp (\ e -> liftM f . g e)

-- | Execute an 'ExprH' using a given interpreter. The given interpretations
-- are tried in order. The first one to match (have the proper type) will be executed.
interpExprH :: CLMonad m => [Interp m b] -> ExprH -> m b
interpExprH interps e = exprToDyns e >>= runInterp e interps

runInterp :: forall m b. CLMonad m => ExprH -> [Interp m b] -> [Dynamic] -> m b
runInterp e interps dyns = case [f a e :: m b | Interp f <- interps, Just a <- map fromDynamic dyns] of
                            []     -> fail $ "Does not type-check: " ++ unparseExprH e ++ "\n"
                            comp:_ -> comp

exprToDyns :: MonadState CommandLineState m => ExprH -> m [Dynamic]
exprToDyns = exprToDyns' False

-- input: list length n, each elem is a variable length list of possible interpretations
-- output: variable length list, each elem is list of length n
fromDynList :: [[Dynamic]] -> [[Dynamic]]
fromDynList [] = [[]]
fromDynList (hs:dynss) = [ h:t | h <- hs, t <- fromDynList dynss ]

toBoxedList :: (Extern a, Typeable b) => [[Dynamic]] -> ([a] -> b) -> [Dynamic]
toBoxedList dyns boxCon = [ toDyn $ boxCon (map unbox l) | dl <- dyns, Just l <- [mapM fromDynamic dl] ]

exprToDyns' :: MonadState CommandLineState m => Bool -> ExprH -> m [Dynamic]
exprToDyns' _   (SrcName str) = do
    let hn = parseName str -- TODO: remove StringBox option below
                           -- TODO: change to SrcName :: HermitName -> ExprH
    return [ toDyn hn, toDyn (BindingName hn), toDyn (OccurrenceName hn), toDyn (RhsOfName hn), toDyn (StringBox str) ]
exprToDyns' _   (CoreH str)   = return [ toDyn $ CoreString str ]
exprToDyns' _   (ListH exprs) = do
    dyns <- liftM fromDynList $ mapM (exprToDyns' True) exprs
    return $    toBoxedList dyns StringListBox
             ++ toBoxedList dyns (PathBox . pathToSnocPath)
                -- ugly hack.  The whole dynamic stuff could do with overhauling.
             ++ toBoxedList dyns (TransformCorePathBox . return . pathToSnocPath)
             ++ toBoxedList dyns IntListBox
             ++ toBoxedList dyns OccurrenceNameListBox
             ++ toBoxedList dyns RewriteCoreListBox
             ++ toBoxedList dyns RuleNameListBox

exprToDyns' rhs (CmdName str)
    | all isDigit str = do
        let i = read str
        return [ -- An Int is either a Path, or will be interpreted specially later.
                 toDyn $ IntBox i
                 -- TODO: Find a better long-term solution.
               , toDyn $ TransformCorePathBox (deprecatedIntToPathT i)
               ]
    | otherwise = do
        dict <- gets (mkDictionary . cl_externals)
        case M.lookup str dict of
            Just dyns           -> do
                dyns' <- mapM provideState dyns
                return $ if rhs then toDyn (StringBox str) : dyns' else dyns'
            -- not a command, try as a string arg... worst case: dynApply fails with "bad type of expression"
            -- best case: 'help ls' works instead of 'help "ls"'. this is likewise done in the clause above
            Nothing | rhs       -> let f = maybe id ((:) . toDyn) $ string2considerable str
                                   in return $ f [ toDyn $ StringBox str
                                                 , toDyn $ LemmaName str
                                                 , toDyn $ RuleName str]
                    | otherwise -> fail $ "User error, unrecognised HERMIT command: " ++ show str
exprToDyns' _ (AppH e1 e2) = liftM2 dynCrossApply (exprToDyns' False e1) (exprToDyns' True e2)

-- We treat externals of the type 'CommandLineState -> b' specially,
-- providing them the shell state here, so they don't need a monadic return type
-- in order to access it themselves.
provideState :: MonadState CommandLineState m => Dynamic -> m Dynamic
provideState dyn = do
    st <- get
    case dynApply dyn (toDyn $ box st) of
        Just d  -> return d
        Nothing -> return dyn

-- Cross product of possible applications.
dynCrossApply :: [Dynamic] -> [Dynamic] -> [Dynamic]
dynCrossApply fs xs = [ r | f <- fs, x <- xs, Just r <- return (dynApply f x)]

-------------------------------------------
