module Main where

import Prelude hiding ((+),map)
import Nat
import Data.Function(fix)

fib :: Nat -> Nat
fib Zero             = Zero
fib (Succ Zero)      = Succ Zero
fib (Succ (Succ n))  = fib (Succ n) + fib n

data Stream a = Cons a (Stream a)

map :: (a -> b) -> Stream a -> Stream b
map f (Cons a s) = Cons (f a) (map f s)

(!!!) :: Stream a -> Nat -> a
(Cons a _) !!! Zero     = a
(Cons _ s) !!! (Succ n) = s !!! n

nats :: Stream Nat
nats = Zero `Cons` map Succ nats

wrap :: Stream a -> (Nat -> a)
wrap = (!!!)

unwrap :: (Nat -> a) -> Stream a
unwrap f = map f nats

{-# RULES "ww" forall f.  fix f = wrap (fix (unwrap . f . wrap)) #-}

main :: IO ()
main = print (fromNat $ fib $ toNat 30)
