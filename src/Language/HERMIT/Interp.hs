{-# LANGUAGE KindSignatures, GADTs, InstanceSigs #-}

module Language.HERMIT.Interp
        ( -- * The HERMIT Interpreter
          Interp
        , interp
        , interpExprH
        ) where

import Control.Monad (liftM, liftM2)

import Data.Char
import Data.Maybe (listToMaybe)
import Data.Dynamic
import qualified Data.Map as M

import qualified Language.Haskell.TH as TH

import Language.HERMIT.External
import Language.HERMIT.Parser
import Language.HERMIT.Core (Crumb)
import Language.HERMIT.Kure (deprecatedIntToPathT)

-- | Interpret an 'ExprH' by looking up the appropriate 'Dynamic'(s) in the provided 'Data.Map', then interpreting the 'Dynamic'(s) with the provided 'Interp's, returning the first interpretation to succeed (or an error string if none succeed).
interpExprH :: M.Map String [Dynamic] -> [Interp a] -> ExprH -> Either String a
interpExprH env interps =
          either Left (\ dyns -> runInterp dyns (map (fmap Right) interps) (Left "User error, HERMIT command does not type-check."))
          . interpExpr env

runInterp :: [Dynamic] -> [Interp b] -> b -> b
runInterp dyns interps bad = head $
             [f a
             | Interp f <- interps
             , Just a <- map fromDynamic dyns
             ] ++ [ bad ]

-- | An 'Interp' @a@ is a /possible/ means of converting a 'Typeable' value to a value of type @a@.
data Interp :: * -> * where
   Interp :: Typeable a => (a -> b) -> Interp b

-- | The primitive way of building an 'Interp'.
interp :: Typeable a => (a -> b) -> Interp b
interp = Interp

instance Functor Interp where
  fmap :: (a -> b) -> Interp a -> Interp b
  fmap f (Interp g) = Interp (f . g)


interpExpr :: M.Map String [Dynamic] -> ExprH -> Either String [Dynamic]
interpExpr = interpExpr' False

-- input: list length n, each elem is a variable length list of possible interpretations
-- output: variable length list, each elem is list of length n
fromDynList :: [[Dynamic]] -> [[Dynamic]]
fromDynList [] = [[]]
fromDynList (hs:dynss) = [ h:t | h <- hs, t <- fromDynList dynss ]

toBoxedList :: (Extern a, Typeable b) => [[Dynamic]] -> ([a] -> b) -> [Dynamic]
toBoxedList dyns boxCon = [ toDyn $ boxCon (map unbox l) | dl <- dyns, Just l <- [mapM fromDynamic dl] ]

interpExpr' :: Bool -> M.Map String [Dynamic] -> ExprH -> Either String [Dynamic]
interpExpr' _   _   (SrcName str) = return [ toDyn $ NameBox $ TH.mkName str ]
interpExpr' _   _   (CoreH str)   = return [ toDyn $ CoreBox (CoreString str) ]
interpExpr' _   env (ListH exprs) = do dyns <- liftM fromDynList $ mapM (interpExpr' True env) exprs
                                       return $    toBoxedList dyns NameListBox
                                                ++ toBoxedList dyns StringListBox
                                                ++ toBoxedList dyns PathBox
interpExpr' rhs env (CmdName str)
                                        -- An Int is either a Path, or will be interpreted specially later.
  | all isDigit str                     = let i = read str in
                                          return [ toDyn $ IntBox i
                                                 , toDyn $ TranslateCorePathBox (deprecatedIntToPathT i) -- TODO: Find a better long-term solution.
                                                 ]
  | Just cr <- (maybeRead str :: Maybe Crumb) = return [ toDyn $ CrumbBox cr ]
  | Just dyn <- M.lookup str env        = return $ if rhs
                                                     then toDyn (StringBox str) : dyn
                                                     else dyn
  -- not a command, try as a string arg... worst case: dynApply fails with "bad type of expression"
  -- best case: 'help ls' works instead of 'help "ls"'. this is likewise done in then clause above
  | rhs                                 = return [toDyn $ StringBox str]
  | otherwise                           = Left $ "User error, unrecognised HERMIT command: " ++ show str
interpExpr' _ env (AppH e1 e2)              = dynAppMsg (interpExpr' False env e1) (interpExpr' True env e2)

dynAppMsg :: Either String [Dynamic] -> Either String [Dynamic] -> Either String [Dynamic]
dynAppMsg = liftM2 dynApply'
   where
           dynApply' :: [Dynamic] -> [Dynamic] -> [Dynamic]
           dynApply' fs xs = [ r | f <- fs, x <- xs, Just r <- return (dynApply f x)]


-------------------------------------------

maybeRead :: Read a => String -> Maybe a
maybeRead = fmap fst . listToMaybe . reads

-------------------------------------------