module Main where

-- We shouldn't need these two, but their definitions are not in scope to inline.
{-# RULES "[] ++"  forall xs.      []     ++ xs = xs             #-}
{-# RULES "(:) ++" forall a as xs. (a:as) ++ xs = a : (as ++ xs) #-}

{-# RULES "++ []" forall xs.  xs ++ [] = xs #-}

main :: IO ()
main = print (replicate 5 True ++ [])
