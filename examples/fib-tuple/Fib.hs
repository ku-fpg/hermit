{-# LANGUAGE CPP #-}
module Main where

import Prelude hiding ((+))

data Nat = Z | S Nat

(+) :: Nat -> Nat -> Nat
Z      + n = n
(S n') + n = S (n' + n)

fromInt :: Int -> Nat
fromInt 0 = Z
fromInt i | i < 0 = error "fromInt negative"
          | otherwise = S (fromInt (i-1))

toInt :: Nat -> Int
toInt Z = 0
toInt (S n) = succ (toInt n)

-- original fib definition
fib :: Nat -> Nat
fib Z = Z
fib (S Z) = S Z
fib (S (S n)) = fib (S n) + fib n

-- goal:
-- fib' = fst work
--   where work Z = (Z, S Z)
--         work (S n) = let (x,y) = work n
--                         in (y,x+y)

wrap :: (Nat -> (Nat, Nat)) -> Nat -> Nat
wrap h n = fst (h n)

unwrap :: (Nat -> Nat) -> Nat -> (Nat, Nat)
unwrap h n = (h n, h (S n))

main :: IO ()
main = print $ toInt $ fib (fromInt 30)
