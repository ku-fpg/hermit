module ReversePrelude
       ( fix
       , H
       , repH
       , absH
       , unwrap
       , wrap 
       ) where

import Data.Function (fix)

type H a = [a] -> [a]

{-# NOINLINE repH #-}
repH :: [a] -> H a
repH xs = (xs ++)

{-# NOINLINE absH #-}
absH :: H a -> [a]
absH f = f []

{-# INLINE unwrap #-}
unwrap :: ([a] -> [a]) -> ([a] -> H a)
unwrap f = repH . f

{-# INLINE wrap #-}
wrap :: ([a] -> H a) -> ([a] -> [a])
wrap g = absH . g




