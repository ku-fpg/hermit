{-# LANGUAGE DataKinds, TypeFamilies, DeriveDataTypeable, FlexibleContexts, TypeSynonymInstances, FlexibleInstances #-}

module Language.HERMIT.External
        ( module Language.HERMIT.External
        , (<>)
        ) where

import GhcPlugins hiding ((<>))

import Language.KURE

import Data.Dynamic
import Data.Monoid
import Language.HERMIT.HermitKure
import Language.HERMIT.HermitMonad
import qualified Language.Haskell.TH as TH
import qualified Data.Map as Map
import Data.Map(Map)


data External = External
        { externName :: String
        , externFun  :: Dynamic
        , externHelp :: [String]
        }
    | Externals [External]

toDictionary :: External -> Map String Dynamic
toDictionary = Map.fromList . toD
  where
         toD (External nm fn help) = [(nm,fn)]
         toD (Externals exts)      = concatMap toD exts

toHelp :: External -> Map String [String]
toHelp = Map.fromList . toH
  where
         toH (External nm fn help) = [(nm,mkHelp nm fn help)]
         toH (Externals exts)      = concatMap toH exts

         mkHelp nm fn help = (nm ++ " :: " ++ show (dynTypeRep fn)) : help

instance Monoid External where
    mempty      = Externals []
    mappend a b = Externals [a,b]

external :: (Extern a) => String -> a -> [String] -> External
external nm fn help = External
        { externName = nm
        , externFun = toDyn (box fn)
        , externHelp = map ("  " ++) help
        }

class (Typeable (Box a)) => Extern a where
    type Box a
    box :: a -> Box a
    unbox :: Box a -> a

instance (Extern a, Extern b) => Extern (a -> b) where
    type Box (a -> b) = Box a -> Box b
    box f a = box (f (unbox a))
    unbox f a = unbox (f (box a))

data IntBox = IntBox Int deriving (Typeable)

instance Extern Int where
    type Box Int = IntBox
    box i = IntBox i
    unbox (IntBox i) = i

data RewriteCoreBox = RewriteCoreBox (RewriteH Core) deriving (Typeable)

instance Extern (RewriteH Core) where
    type Box (RewriteH Core) = RewriteCoreBox
    box i = RewriteCoreBox i
    unbox (RewriteCoreBox i) = i

data TranslateCoreStringBox = TranslateCoreStringBox (TranslateH Core String) deriving (Typeable)

instance Extern (TranslateH Core String) where
    type Box (TranslateH Core String) = TranslateCoreStringBox
    box i = TranslateCoreStringBox i
    unbox (TranslateCoreStringBox i) = i

data NameBox = NameBox (TH.Name) deriving (Typeable)

instance Extern TH.Name where
    type Box TH.Name = NameBox
    box i = NameBox i
    unbox (NameBox i) = i

data LensCoreCoreBox = LensCoreCoreBox (LensH Core Core)
        deriving (Typeable)

instance Extern (LensH Core Core) where
    type Box (LensH Core Core) = LensCoreCoreBox
    box i = LensCoreCoreBox i
    unbox (LensCoreCoreBox i) = i
