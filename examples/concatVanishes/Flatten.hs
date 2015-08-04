{-# LANGUAGE CPP #-}
module Main where

import HList

data Tree a = Node (Tree a) (Tree a) | Leaf a

flatten :: Tree a -> [a]
flatten (Leaf a)   = [a]
flatten (Node l r) = flatten l ++ flatten r

main :: IO ()
main = print (flatten (Node (Leaf 'h') (Leaf 'i')))


-- Should be in the "List" module
{-# RULES "++ []"  forall xs .  xs ++ [] = xs #-}
{-# RULES "++ strict"           (++) undefined = undefined #-}

-- The "Algebra" for repH
{-# RULES "repH ++" forall xs ys .     repH (xs ++ ys) = repH xs . repH ys #-}
{-# RULES "repH []"                    repH [] = id                        #-}
{-# RULES "repH (:)" forall x xs .     repH (x:xs) = ((:) x) . repH xs     #-}

