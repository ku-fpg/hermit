module FibPrelude (fix, absF, repF, wrap, unwrap, Nat) where

-- so we can fix-intro
import Data.Function (fix)

-- we need a better way for when we need to case on Nat
type Nat = Int

{-# NOINLINE absF #-}
absF :: (Nat -> (Nat, Nat)) -> Nat -> Nat
absF h = fst . h

{-# NOINLINE repF #-}
repF :: (Nat -> Nat) -> Nat -> (Nat, Nat)
repF h n = (h n, h (n+1))

--unwrap :: forall a. (a -> Nat -> Nat) -> a -> Nat -> (Nat, Nat)
{-# INLINE unwrap #-}
unwrap f = repF . f

--wrap :: forall a. (a -> Nat -> (Nat, Nat)) -> a -> Nat -> Nat
{-# INLINE wrap #-}
wrap g = absF . g
