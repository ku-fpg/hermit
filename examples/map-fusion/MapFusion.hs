module MapFusion where

import Prelude hiding (map)

{-# RULES "map-fusion" forall f g.  map f . map g = map (f . g)  #-}

map :: (a -> b) -> [a] -> [b]
map f []     = []
map f (a:as) = f a : map f as
