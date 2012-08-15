module Main where

import Prelude hiding ((+))
import GHC.Tuple
import Data.Function (fix)
import Nat

fib :: Nat -> Nat
fib Zero             = Zero
fib (Succ Zero)      = Succ Zero
fib (Succ (Succ n))  = fib (Succ n) + fib n

wrap :: (Nat -> (Nat, Nat)) -> Nat -> Nat
wrap h = fst . h

unwrap :: (Nat -> Nat) -> Nat -> (Nat, Nat)
unwrap h n = (h n, h (Succ n))

{-# RULES "ww" forall f.  fix f = wrap (fix (unwrap . f . wrap)) #-}
{-# RULES "precondition" forall w.  wrap (unwrap w) = w          #-}

main :: IO ()
main = print (fromNat $ fib $ toNat 30)
