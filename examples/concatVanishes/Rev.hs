{-# LANGUAGE CPP #-}
module Main where

import HList

rev :: [a] -> [a]
rev []     = []
rev (y:ys) = rev ys ++ [y]

main :: IO ()
main = print $ rev [1..10]


-- Should be in the "List" module
{-# RULES "++ []"  forall xs .  xs ++ [] = xs #-}
{-# RULES "++ strict"           (++) undefined = undefined #-}

-- The "Algebra" for repH
{-# RULES "repH ++" forall xs ys .     repH (xs ++ ys) = repH xs . repH ys #-}
{-# RULES "repH []"                    repH [] = id                        #-}
{-# RULES "repH (:)" forall x xs .     repH (x:xs) = ((:) x) . repH xs     #-}

