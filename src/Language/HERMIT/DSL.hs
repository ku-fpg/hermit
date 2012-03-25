{-# LANGUAGE TypeFamilies, FlexibleInstances, GADTs, TemplateHaskell #-}

-- | The GHC-facing DSL interface for HERMIT, which controls the transformation engine.

module Language.HERMIT.DSL where

import Data.Monoid
import Language.Haskell.TH.Syntax as Syn

-- There is a relationship between this DSL,
-- and the Hermitage API.
-- TO CONSIDER: Maybe they can be merged.
-- We could use an 'H a' here, where a is the object under consideration.

-- The deep embedding of our DSL
data H :: * where
        Consider        :: Syn.Name -> [H]              -> H
        Apply           :: String                       -> H

        -- Monoid embedding.
        Seq             :: [H]                          -> H

instance Monoid H where
        mempty      = Seq []
        mappend a b = Seq [a,b]
        mconcat xs  = Seq xs

-- 'consider' restricts the syntax tree under consideration
consider :: Syn.Name -> [H] -> H
consider = Consider

-- 'apply' applies a named transform *here*.
apply :: String -> H
apply = Apply

instance Show H where
        show (Consider nm h) = "consider " ++ show nm ++ show h
        show (Apply nm)      = "apply " ++ show nm
        show (Seq hs)        = show hs
