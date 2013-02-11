module Nat where

import Prelude hiding ((+))

data Nat = Zero | Succ Nat deriving (Eq,Show)

(+) :: Nat -> Nat -> Nat
Zero     + n = n
(Succ m) + n = Succ (m + n)

toNat :: Integer -> Nat
toNat 0 = Zero
toNat n = Succ (toNat (pred n))

fromNat :: Nat -> Integer
fromNat Zero = 0
fromNat (Succ n) = succ (fromNat n)