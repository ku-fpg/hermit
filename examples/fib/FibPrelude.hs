module FibPrelude (fix, wrap, unwrap, Nat(..)) where

-- so we can fix-intro
import Data.Function (fix)

-- we need a better way for when we need to case on Nat
data Nat = Zero | Succ Nat

instance Num Nat where
    n1 + Zero = n1
    n1 + (Succ n2) = Succ (n1 + n2)
    fromInteger 0 = Zero
    fromInteger i = Succ (fromInteger (i-1))

{-# INLINE wrap #-}
wrap :: (Nat -> (Nat, Nat)) -> Nat -> Nat
wrap h = fst . h

{-# INLINE unwrap #-}
unwrap :: (Nat -> Nat) -> Nat -> (Nat, Nat)
unwrap h n = (h n, h (Succ n))
