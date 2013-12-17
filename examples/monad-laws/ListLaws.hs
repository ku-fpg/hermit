module ListLaws where

import Prelude hiding (map,id, concat, (++))

{-# RULES "left-unit"  forall x f.  retur x `bind` f  =  f x  #-}

{-# RULES "right-unit"  forall m.   m `bind` retur  =  m  #-}

{-# RULES "monad-assoc" forall m f g.  (m `bind` f) `bind` g  =  m `bind` \x -> (f x `bind` g) #-}

{-# RULES "monoid-left" forall x.  mempt `mappen` x = x  #-}

{-# RULES "monoid-right" forall x.  x `mappen` mempt = x  #-}

{-# RULES "monoid-assoc" forall x y z.  x `mappen` (y `mappen` z) = (x `mappen` y) `mappen` z #-}

{-# RULES "nil-append"  forall xs.  [] ++ xs = xs #-}
{-# RULES "append-nil"  forall xs.  xs ++ [] = xs #-}
{-# RULES "cons-append" forall a as xs. (a:as) ++ xs = a : (as ++ xs) #-}
{-# RULES "append-assoc" forall x y z. x ++ (y ++ z) = (x++y) ++ z #-}


{-# RULES "concat-unit"  forall x. concat [x] = x  #-}
{-# RULES "concat-of-toList"  forall xs. concat (map toList xs) = xs  #-}


bind :: [a] -> (a -> [b]) -> [b]
bind [] k = []
bind as@(a1:arest) k = concat (map k as)

retur :: a -> [a]
retur = toList

toList :: a -> [a]
toList x = [x]

(++) :: [a] -> [a] -> [a]
(++) []     ys = ys
(++) (x:xs) ys = x : xs ++ ys

map :: (a -> b) -> [a] -> [b]
map _ []     = []
map f (a:as) = f a : map f as

concat :: [[a]] -> [a]
concat [] = []
concat (x:xs) =  x ++ (concat xs)

mempt :: [a]
mempt = []

mappen :: [a] -> [a] -> [a]
mappen xs ys = xs ++ ys
