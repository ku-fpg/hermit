module Main where

-- So that we can use the worker/wrapper transformation.
import Data.Function (fix)

import Prelude hiding ((+))
import Nat

--------------------------------------------

fib :: Nat -> Nat
fib Zero             = Zero
fib (Succ Zero)      = Succ Zero
fib (Succ (Succ n))  = fib (Succ n) + fib n

--------------------------------------------

main :: IO ()
main = print (fromNat $ fib $ toNat 30)

--------------------------------------------

wrap :: (Nat -> (Nat, Nat)) -> Nat -> Nat
wrap h n = fst (h n)

unwrap :: (Nat -> Nat) -> Nat -> (Nat, Nat)
unwrap h n = (h n, h (Succ n))

--------------------------------------------
