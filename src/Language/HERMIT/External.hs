{-# LANGUAGE TypeFamilies, DeriveDataTypeable, FlexibleContexts, TypeSynonymInstances, FlexibleInstances #-}

module Language.HERMIT.External where

import Data.Map hiding (map)
import Data.Dynamic

import qualified Language.Haskell.TH as TH

import Language.HERMIT.HermitKure
import Language.HERMIT.Kernel

-----------------------------------------------------------------

type ExternalName = String
type ExternalHelp = [String]

data External = External
        { externName :: ExternalName
        , externFun  :: Dynamic
        , externHelp :: ExternalHelp
        }

external :: Extern a => ExternalName -> a -> ExternalHelp -> External
external nm fn help = External
        { externName = nm
        , externFun  = toDyn (box fn)
        , externHelp = map ("  " ++) help
        }

toDictionary :: [External] -> Map ExternalName Dynamic
toDictionary = fromListWithKey (\ k _ _ -> error $ "HERMIT Command Redefined: " ++ k) . map toD
  where
         toD :: External -> (ExternalName,Dynamic)
         toD (External nm fn _) = (nm,fn)

toHelp :: [External] -> Map ExternalName ExternalHelp
toHelp = fromList . map toH
  where
         toH :: External -> (ExternalName,ExternalHelp)
         toH (External nm fn help) = (nm, (nm ++ " :: " ++ show (dynTypeRep fn)) : help)

-----------------------------------------------------------------

class Typeable (Box a) => Extern a where
    type Box a
    box :: a -> Box a
    unbox :: Box a -> a

instance (Extern a, Extern b) => Extern (a -> b) where
    type Box (a -> b) = Box a -> Box b
    box f = box . f . unbox
    unbox f = unbox . f . box

data IntBox = IntBox Int deriving Typeable

instance Extern Int where
    type Box Int = IntBox
    box i = IntBox i
    unbox (IntBox i) = i

data RewriteCoreBox = RewriteCoreBox (RewriteH Core) deriving Typeable

instance Extern (RewriteH Core) where
    type Box (RewriteH Core) = RewriteCoreBox
    box i = RewriteCoreBox i
    unbox (RewriteCoreBox i) = i

data TranslateCoreStringBox = TranslateCoreStringBox (TranslateH Core String) deriving Typeable

instance Extern (TranslateH Core String) where
    type Box (TranslateH Core String) = TranslateCoreStringBox
    box i = TranslateCoreStringBox i
    unbox (TranslateCoreStringBox i) = i

data NameBox = NameBox (TH.Name) deriving Typeable

instance Extern TH.Name where
    type Box TH.Name = NameBox
    box i = NameBox i
    unbox (NameBox i) = i

data LensCoreCoreBox = LensCoreCoreBox (LensH Core Core) deriving Typeable

instance Extern (LensH Core Core) where
    type Box (LensH Core Core) = LensCoreCoreBox
    box i = LensCoreCoreBox i
    unbox (LensCoreCoreBox i) = i

data KernelCommandBox = KernelCommandBox KernelCommand deriving Typeable

instance Extern KernelCommand where
    type Box KernelCommand = KernelCommandBox
    box i = KernelCommandBox i
    unbox (KernelCommandBox i) = i

data Help = Help deriving Typeable

instance Extern Help where
    type Box Help = Help
    box i = i
    unbox i = i

data StringBox = StringBox String deriving Typeable

instance Extern String where
    type Box String = StringBox
    box i = StringBox i
    unbox (StringBox i) = i

-----------------------------------------------------------------
