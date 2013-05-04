{-# LANGUAGE DeriveDataTypeable    #-}

module Auxiliary.Nat (
    Nat(..), eqNat, toInt
  ) where

import Data.Generics

-- Nat datatype
data Nat = Ze | Su Nat deriving (Typeable, Show, Eq)

eqNat :: Nat -> Nat -> Bool
eqNat Ze Ze = True
eqNat (Su m) (Su n) = eqNat m n
eqNat _ _ = False

toInt :: Nat -> Int
toInt Ze = 0
toInt (Su n) = 1 + toInt n
