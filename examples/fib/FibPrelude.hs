module FibPrelude (fix, wrap, unwrap, Nat) where

-- so we can fix-intro
import Data.Function (fix)

-- we need a better way for when we need to case on Nat
type Nat = Int

{-# INLINE wrap #-}
wrap :: (Nat -> (Nat, Nat)) -> Nat -> Nat
wrap h = fst . h

{-# INLINE unwrap #-}
unwrap :: (Nat -> Nat) -> Nat -> (Nat, Nat)
unwrap h n = (h n, h (n+1))
