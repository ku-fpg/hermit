module HERMIT 
       ( fix
       , H
       , repH
       , absH
       , unwrap
       , wrap 
       ) where

import Data.Function (fix)

type H a = [a] -> [a]

repH :: [a] -> H a
repH xs = (xs ++)

absH :: H a -> [a]
absH f = f []

unwrap :: ([a] -> [a]) -> ([a] -> H a)
unwrap f = repH . f

wrap :: ([a] -> H a) -> ([a] -> [a])
wrap g = absH . g




