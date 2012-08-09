import Prelude hiding ((+))
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

main :: IO ()
main = print (fromNat $ fib $ toNat 30)