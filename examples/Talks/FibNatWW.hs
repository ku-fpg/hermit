module Main where

import Prelude hiding ((+))
import Data.Function (fix)
import Nat

fib :: Nat -> Nat
fib Zero             = Zero
fib (Succ Zero)      = Succ Zero
fib (Succ (Succ n))  = fib (Succ n) + fib n

{-# INLINE wrap #-}
wrap :: (Nat -> (Nat, Nat)) -> Nat -> Nat
wrap h = fst . h

{-# INLINE unwrap #-}
unwrap :: (Nat -> Nat) -> Nat -> (Nat, Nat)
unwrap h n = (h n, h (Succ n))

{-# RULES "ww" forall f . fix f = wrap (fix (unwrap . f . wrap)) #-}

main :: IO ()
main = print (fromNat $ fib $ toNat 30)