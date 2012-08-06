module Main where

import HList
import Data.Function (fix)

data Tree a = Node (Tree a) (Tree a) | Leaf a

{-# INLINE unwrap #-}
unwrap :: (Tree a -> [a]) -> (Tree a -> H a)
unwrap f = repH . f

{-# INLINE wrap #-}
wrap :: (Tree a -> H a) -> (Tree a -> [a])
wrap g = absH . g

{-# RULES "ww" forall f . fix f = wrap (fix (unwrap . f . wrap)) #-}
{-# RULES "inline-fix" forall f . fix f = let w = f w in w #-}

-- flatten :: Tree a -> [a]
flatten (Leaf a)   = [a]
flatten (Node l r) = flatten l ++ flatten r

main :: IO ()
main = print (flatten (Node (Leaf 'h') (Leaf 'i')))

