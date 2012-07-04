module HList
       ( H
       , repH
       , absH
       ) where

type H a = [a] -> [a]

{-# INLINE repH #-}
repH :: [a] -> H a
repH xs = (xs ++)

{-# INLINE absH #-}
absH :: H a -> [a]
absH f = f []

-- These two we may get for free via INLINE
{-# RULES "repH" forall xs	 . repH xs = (xs ++) #-}
{-# RULES "absH" forall f 	 . absH f = f []     #-}

-- The "Algebra" for repH
{-# RULES "repH ++" forall xs ys . repH (xs ++ ys) = repH xs . repH ys #-}
{-# RULES "repH []" 	           repH [] = ([] ++) 	       	       #-}
{-# RULES "repH (:)" forall x xs   . repH (x:xs) = ((:) x) . repH xs     #-}

-- Should be in the "List" module
{-# RULES "(:) ++" forall x xs ys . (x:xs) ++ ys = x : (xs ++ ys) #-}
{-# RULES "[] ++"  forall xs . [] ++ xs = xs #-}

-- has preconditon
{-# RULES "rep-abs-fusion" forall h . repH (absH h) = h #-}





