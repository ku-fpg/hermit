{-# LANGUAGE UnicodeSyntax #-}

import Prelude hiding (abs)
import Data.Set hiding (filter)
import Data.Function (fix)

type ℤ = Int
type List = []

nub :: List ℤ → List ℤ
nub [] = []
nub (x : xs) = x : nub (filter (/= x) xs)

work :: List ℤ → Set ℤ → List ℤ
work []       s = []
work (x : xs) s = let ys = work xs (insert x s)
                   in if x `member` s then ys else x : ys

f :: (List ℤ → List ℤ) → List ℤ → List ℤ
f h [] = []
f h (x : xs) = x : h (filter (/= x) xs)

g :: (List ℤ → Set ℤ → List ℤ) → List ℤ → Set ℤ → List ℤ
g h []       s = []
g h (x : xs) s = let ys = h xs (insert x s)
                  in if x `member` s then ys else x : ys

abs :: (List ℤ → Set ℤ → List ℤ) → List ℤ → List ℤ
abs h [] = []
abs h (x:xs) = x : h xs (singleton x)

rep :: (List ℤ → List ℤ) → List ℤ → Set ℤ → List ℤ
rep h xs s = h (filter (`notMember` s) xs)

--------------------------------------------------
