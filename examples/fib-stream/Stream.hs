module Stream where

import Prelude hiding (map,(!!))
import Nat

data Stream a = Cons a (Stream a)

map :: (a -> b) -> Stream a -> Stream b
map f (Cons a s) = Cons (f a) (map f s)

(!!) :: Stream a -> Nat -> a
(Cons a _) !! Zero     = a
(Cons _ s) !! (Succ n) = s !! n

nats :: Stream Nat
nats = Zero `Cons` map Succ nats
