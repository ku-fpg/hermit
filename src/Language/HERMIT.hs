{-# LANGUAGE KindSignatures, GADTs, TemplateHaskell #-}
module Language.HERMIT where

import Language.Haskell.TH.Syntax as Syn


-- The deep embedding of our DSL
data Cmd :: * -> * where
        Consider :: Syn.Name -> Cmd ()

-- The functions that implement the DSL
consider :: Syn.Name -> Cmd ()
consider = Consider
