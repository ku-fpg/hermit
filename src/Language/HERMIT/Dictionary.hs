{-# LANGUAGE KindSignatures, GADTs #-}
-- The main namespace. Things tend to be untyped, because the API is accessed via (untyped) names.

module Language.HERMIT.Dictionary where

import Prelude hiding (lookup)

import Data.Map
import Data.Char
import Data.Dynamic

import Control.Monad (liftM2)

import qualified Language.Haskell.TH as TH

import Language.KURE

import Language.HERMIT.HermitExpr
import Language.HERMIT.Kernel
import Language.HERMIT.External

import qualified Language.HERMIT.Primitive.Command as Command
import qualified Language.HERMIT.Primitive.Kure as Kure
import qualified Language.HERMIT.Primitive.Consider as Consider
import qualified Language.HERMIT.Primitive.Inline as Inline
import qualified Language.HERMIT.Primitive.Case as Case
import qualified Language.HERMIT.Primitive.Subst as Subst
import qualified Language.HERMIT.Primitive.Local as Local
import qualified Language.HERMIT.Primitive.New as New

--------------------------------------------------------------------------

all_externals :: [External]
all_externals =    Command.externals
                ++ Kure.externals
                ++ Consider.externals
                ++ Inline.externals
                ++ Case.externals
                ++ Subst.externals
                ++ Local.externals
                ++ New.externals

dictionary :: Map String Dynamic
dictionary = toDictionary all_externals

help :: [String]
help = concatMap snd $ toList $ toHelp all_externals

--------------------------------------------------------------------------

-- The union of all possible results from a "well-typed" commands, from this dictionary.

interpExprH :: ExprH -> Either String KernelCommand
interpExprH expr =
        case interpExpr' expr of
          Left msg  -> Left msg
          Right dyn -> runInterp dyn
             [ Interp $ \ (KernelCommandBox cmd)      -> Right cmd
             , Interp $ \ (RewriteCoreBox rr)         -> Right $ Apply rr
             , Interp $ \ (TranslateCoreStringBox tt) -> Right $ Query tt
             , Interp $ \ (LensCoreCoreBox l)         -> Right $ PushFocus l
             , Interp $ \ (IntBox i)                  -> Right $ PushFocus $ chooseL i
             , Interp $ \ Help                        -> Left  $ unlines help
             ]
             (Left "interpExpr: bad type of expression")

data Interp :: * -> * where
   Interp :: Typeable a => (a -> b) -> Interp b

runInterp :: Dynamic -> [Interp b] -> b -> b
runInterp _   []                bad = bad
runInterp dyn (Interp f : rest) bad = maybe (runInterp dyn rest bad) f (fromDynamic dyn)

--------------------------------------------------------------------------

interpExpr' :: ExprH -> Either String Dynamic
interpExpr' (SrcName str) = Right $ toDyn $ NameBox $ TH.mkName str
interpExpr' (CmdName str)
  | all isDigit str                   = Right $ toDyn $ IntBox $ read str
  | Just dyn <- lookup str dictionary = Right dyn
  | otherwise                         = Left $ "Unrecognised command: " ++ show str
interpExpr' (AppH e1 e2) = dynAppMsg (interpExpr' e1) (interpExpr' e2)

dynAppMsg :: Either String Dynamic -> Either String Dynamic -> Either String Dynamic
dynAppMsg f x = liftM2 dynApply f x >>= maybe (Left "apply failed") Right

--------------------------------------------------------------------------
