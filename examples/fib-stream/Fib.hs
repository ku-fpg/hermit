{-# LANGUAGE CPP #-}
module Main where

import Prelude hiding ((+),map,(!!))
import Nat
import Stream

#if __GLASGOW_HASKELL__ < 708
import Data.Function (fix)
#endif

fib :: Nat -> Nat
fib Zero             = Zero
fib (Succ Zero)      = Succ Zero
fib (Succ (Succ n))  = fib (Succ n) + fib n

wrap :: Stream a -> (Nat -> a)
wrap s n = s !! n

unwrap :: (Nat -> a) -> Stream a
unwrap f = map f nats

main :: IO ()
main = print (fromNat $ fib $ toNat 30)
