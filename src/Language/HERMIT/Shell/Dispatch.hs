{-# LANGUAGE FlexibleInstances, ScopedTypeVariables, GADTs, KindSignatures, TypeFamilies, DeriveDataTypeable #-}

module Language.HERMIT.Shell.Dispatch where

import Prelude hiding (catch)

import GhcPlugins hiding (L)

import Data.Char
import Data.Dynamic
import Control.Applicative
import Control.Arrow
import Data.List (intercalate)
import Data.Default (def)
import Control.Exception.Base hiding (catch)

import qualified Data.Map as M
import qualified Text.PrettyPrint.MarkedHughesPJ as PP
import System.Console.ANSI

import Language.HERMIT.HermitExpr
import Language.HERMIT.HermitEnv
import Language.HERMIT.HermitKure
import Language.HERMIT.Dictionary
import Language.HERMIT.Kernel
import Language.HERMIT.PrettyPrinter
import Language.HERMIT.Interp
import Language.HERMIT.Shell.Command


