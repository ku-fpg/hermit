{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE UndecidableInstances  #-}

module Auxiliary.SYB3 where

import Auxiliary.Tree (Tree(..))
import Auxiliary.Logic (Logic(..))
import Data.Generics.SYB.WithClass.Basics
import Data.Generics.SYB.WithClass.Derive (deriveData)
import Data.Generics.SYB.WithClass.Instances ()

$(deriveData  [''Tree, ''Logic])
