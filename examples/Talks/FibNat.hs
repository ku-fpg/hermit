import Prelude hiding ((+))
import Nat

fib :: Nat -> Nat
fib Zero             = Zero
fib (Succ Zero)      = Succ Zero
fib (Succ (Succ n))  = fib (Succ n) + fib n

main :: IO ()
main = print (fromNat $ fib $ toNat 30)