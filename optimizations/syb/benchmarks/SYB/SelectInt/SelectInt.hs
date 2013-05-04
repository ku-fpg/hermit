{-# LANGUAGE RankNTypes #-}
module SYB.SelectInt.SelectInt where

import Data.Generics
import TreeDatatype

selectInt_acc :: Data a => a -> [Int]
-- selectInt_acc x = everything (.) (mkQ id (:)) x []
selectInt_acc x = everythingAcc (mkQ id (:)) x []

everythingAcc :: GenericQ (r -> r) -> GenericQ (r -> r)
everythingAcc f x acc =
  gmapQr ($) (f x acc) (everythingAcc f) x

{-
r' = r -> r
gmapQr :: forall r r'. (r' -> r -> r) -> r -> (forall d. Data d => d -> r') -> a -> r
  gmapQr o r0 f x0 = unQr (gfoldl k (const (Qr id)) x0) r0
    where
      k :: Data d => Qr r (d->b) -> d -> Qr r b
      k (Qr c) x = Qr (\r -> c (f x `o` r))
-}
