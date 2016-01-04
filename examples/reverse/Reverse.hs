{-# LANGUAGE CPP #-}
module Main where

import HList
-- import Seq

rev :: [a] -> [a]
rev []     = []
rev (x:xs) = rev xs ++ [x]

main :: IO ()
main = print $ rev "hello"


-- Should be in a "List" module
{-# RULES "++ []"  forall xs .  xs ++ [] = xs #-}
{-# RULES "++ strict"           (++) undefined = undefined #-}

-- The "Algebra" for repH
{-# RULES "repH ++" forall xs ys   . repH (xs ++ ys) = repH xs . repH ys #-}
{-# RULES "repH []"                  repH [] = id                        #-}
{-# RULES "repH (:)" forall x xs   . repH (x:xs) = ((:) x) . repH xs     #-}
