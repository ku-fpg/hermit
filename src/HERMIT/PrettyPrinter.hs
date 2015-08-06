{-# LANGUAGE OverloadedStrings #-}
module HERMIT.PrettyPrinter where

import Data.Aeson

import HERMIT.PrettyPrinter.Common
import qualified HERMIT.PrettyPrinter.AST as AST
import qualified HERMIT.PrettyPrinter.Clean as Clean
import qualified HERMIT.PrettyPrinter.GHC as GHC

instance ToJSON PrettyPrinter where
    toJSON (PP _ _ opts tag) = object ["opts" .= opts, "tag" .= tag]

instance FromJSON PrettyPrinter where
    parseJSON (Object v) =
      do opts <- v .: "opts"
         tag <- v .: "tag"
         case tag of
           "ast"   -> return $! PP AST.ppForallQuantification
                                   AST.ppCoreTC opts tag
           "clean" -> return $! PP Clean.ppForallQuantification
                                   Clean.ppCoreTC opts tag
           "ghc"   -> return $! PP GHC.ppForallQuantification
                                   GHC.ppCoreTC opts tag
