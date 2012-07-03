module HanoiPrelude (fix, wrap, unwrap, Nat) where

-- so we can fix-intro
import Data.Function (fix)

-- we need a better way for when we need to case on Nat
type Nat = Int

{-# INLINE wrap #-}
-- wrap :: todo
wrap h = error "todo: wrap"

{-# INLINE unwrap #-}
-- unwrap :: todo
unwrap h n = error "todo: unwrap"
