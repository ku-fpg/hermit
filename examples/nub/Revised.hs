{-# LANGUAGE CPP #-}
{-# LANGUAGE UnicodeSyntax #-}

import Prelude hiding (abs)
import Data.Set hiding (filter)
#if __GLASGOW_HASKELL__ < 708
import Data.Function (fix)
#endif

type ℤ = Int
type List = []

nub :: List ℤ → List ℤ
nub [] = []
nub (x : xs) = x : nub (filter (/= x) xs)

work :: List ℤ → Set ℤ → List ℤ
work []       s = []
work (x : xs) s = if x `member` s then work xs s else x : work xs (insert x s)

f :: (List ℤ → List ℤ) → List ℤ → List ℤ
f h [] = []
f h (x : xs) = x : h (filter (/= x) xs)

g :: (List ℤ → Set ℤ → List ℤ) → List ℤ → Set ℤ → List ℤ
g h []       s = []
g h (x : xs) s = if x `member` s then h xs s else x : h xs (insert x s)

abs :: (List ℤ → Set ℤ → List ℤ) → List ℤ → List ℤ
abs h [] = []
abs h (x:xs) = x : h xs (singleton x)

rep :: (List ℤ → List ℤ) → List ℤ → Set ℤ → List ℤ
rep h xs s = h (filter (`notMember` s) xs)

--------------------------------------------------
