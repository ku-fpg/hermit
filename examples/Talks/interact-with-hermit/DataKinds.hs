{-# LANGUAGE GADTs, KindSignatures, DataKinds, TypeFamilies, TypeOperators #-}

module Main where

import Prelude hiding ((++),zipWith)


data Nat = Zero | Succ Nat


data Vec :: * -> Nat -> * where
  Nil  ::                 Vec a Zero
  Cons :: a -> Vec a n -> Vec a (Succ n)


type family   (m :: Nat) :+: (n :: Nat) :: Nat
type instance Zero       :+: n          =  n
type instance (Succ m)   :+: n          =  Succ (m :+: n)


(++) :: Vec a m -> Vec a n -> Vec a (m :+: n)
Nil           ++ bs = bs
(a `Cons` as) ++ bs = a `Cons` (as ++ bs)

zipWith :: (a -> b -> c) -> Vec a n -> Vec b n -> Vec c n
zipWith f Nil Nil = Nil
zipWith f (Cons a as) (Cons b bs) = Cons (f a b) (zipWith f as bs)

------------------------------------------------

main :: IO ()
main = print "hello world"

------------------------------------------------
