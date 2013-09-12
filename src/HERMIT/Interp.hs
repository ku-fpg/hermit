{-# LANGUAGE KindSignatures, GADTs, InstanceSigs #-}

module HERMIT.Interp
        ( -- * The HERMIT Interpreter
          Interp
        , interp
        , interpExprH
        ) where

import Control.Monad (liftM, liftM2)

import Data.Char
import Data.Dynamic
import qualified Data.Map as M

import qualified Language.Haskell.TH as TH

import HERMIT.External
import HERMIT.Parser
import HERMIT.Kure (deprecatedIntToPathT,pathToSnocPath)

-- | Interpret an 'ExprH' by looking up the appropriate 'Dynamic'(s) in the provided 'Dictionary', then interpreting the 'Dynamic'(s) with the provided 'Interp's, returning the first interpretation to succeed (or an error string if none succeed).
interpExprH :: Monad m => Dictionary -> [Interp a] -> ExprH -> m a
interpExprH dict interps e = do dyns <- interpExpr dict e
                                runInterp dyns interps

runInterp :: Monad m => [Dynamic] -> [Interp b] -> m b
runInterp dyns interps = case [f a | Interp f <- interps, Just a <- map fromDynamic dyns] of
                           []  -> fail "User error, HERMIT command does not type-check."
                           b:_ -> return b

-- | An 'Interp' @a@ is a /possible/ means of converting a 'Typeable' value to a value of type @a@.
data Interp :: * -> * where
   Interp :: Typeable a => (a -> b) -> Interp b

-- | The primitive way of building an 'Interp'.
interp :: Typeable a => (a -> b) -> Interp b
interp = Interp

instance Functor Interp where
  fmap :: (a -> b) -> Interp a -> Interp b
  fmap f (Interp g) = Interp (f . g)


interpExpr :: Monad m => Dictionary -> ExprH -> m [Dynamic]
interpExpr = interpExpr' False

-- input: list length n, each elem is a variable length list of possible interpretations
-- output: variable length list, each elem is list of length n
fromDynList :: [[Dynamic]] -> [[Dynamic]]
fromDynList [] = [[]]
fromDynList (hs:dynss) = [ h:t | h <- hs, t <- fromDynList dynss ]

toBoxedList :: (Extern a, Typeable b) => [[Dynamic]] -> ([a] -> b) -> [Dynamic]
toBoxedList dyns boxCon = [ toDyn $ boxCon (map unbox l) | dl <- dyns, Just l <- [mapM fromDynamic dl] ]

interpExpr' :: Monad m => Bool -> Dictionary -> ExprH -> m [Dynamic]
interpExpr' _   _    (SrcName str) = return [ toDyn $ NameBox $ TH.mkName str ]
interpExpr' _   _    (CoreH str)   = return [ toDyn $ CoreBox (CoreString str) ]
interpExpr' _   dict (ListH exprs) = do dyns <- liftM fromDynList $ mapM (interpExpr' True dict) exprs
                                        return $    toBoxedList dyns NameListBox
                                                 ++ toBoxedList dyns StringListBox
                                                 ++ toBoxedList dyns (PathBox . pathToSnocPath)
                                                 ++ toBoxedList dyns IntListBox
                                                 ++ toBoxedList dyns RewriteCoreListBox
interpExpr' rhs dict (CmdName str)
                                        -- An Int is either a Path, or will be interpreted specially later.
  | all isDigit str                     = let i = read str in
                                          return [ toDyn $ IntBox i
                                                 , toDyn $ TranslateCorePathBox (deprecatedIntToPathT i) -- TODO: Find a better long-term solution.
                                                 ]
  | Just dyn <- M.lookup str dict       = return $ if rhs
                                                     then toDyn (StringBox str) : dyn
                                                     else dyn
  -- not a command, try as a string arg... worst case: dynApply fails with "bad type of expression"
  -- best case: 'help ls' works instead of 'help "ls"'. this is likewise done in the clause above
  | rhs                                 = return [toDyn $ StringBox str]
  | otherwise                           = fail $ "User error, unrecognised HERMIT command: " ++ show str
interpExpr' _ env (AppH e1 e2)          = dynAppMsg (interpExpr' False env e1) (interpExpr' True env e2)

dynAppMsg :: Monad m => m [Dynamic] -> m [Dynamic] -> m [Dynamic]
dynAppMsg = liftM2 dynApply'
   where
           dynApply' :: [Dynamic] -> [Dynamic] -> [Dynamic]
           dynApply' fs xs = [ r | f <- fs, x <- xs, Just r <- return (dynApply f x)]

-------------------------------------------
