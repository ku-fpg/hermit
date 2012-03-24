{-# LANGUAGE TypeFamilies, FlexibleInstances, GADTs, TemplateHaskell #-}

-- | The GHC-facing DSL interface for HERMIT, which controls the transformation engine.

module Language.HERMIT.DSL where

import Language.Haskell.TH.Syntax as Syn

-- The deep embedding of our DSL
data H :: * -> * where
        Consider        :: Syn.Name -> H ()             -> H ()
        Apply           :: String                       -> H ()
        Return          :: a                            -> H a
        Bind            :: H a -> (a -> H b)            -> H b

instance Monad H where
        return = Return
        (>>=) = Bind

-- 'consider' restricts the syntax tree under consideration
consider :: Syn.Name -> H () ->  H ()
consider = Consider

-- 'apply' applies a named transform *here*.
apply :: String -> H ()
apply = Apply

