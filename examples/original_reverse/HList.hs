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

-- Because we can't get unfolding for ++
myAppend :: [a] -> [a] -> [a]
myAppend []     ys = ys
myAppend (x:xs) ys = x : myAppend xs ys
{-# RULES "appendFix" forall xs ys. xs ++ ys = myAppend xs ys #-}

-- These two we may get for free via INLINE
{-# RULES "repH" forall xs       . repH xs = (xs ++) #-}
{-# RULES "absH" forall f        . absH f = f []     #-}

-- The "Algebra" for repH
{-# RULES "repH ++" forall xs ys   . repH (xs ++ ys) = repH xs . repH ys #-}
{-# RULES "repH []"                  repH [] = id                        #-}
{-# RULES "repH (:)" forall x xs   . repH (x:xs) = ((:) x) . repH xs     #-}

-- Should be in the "List" module
{-# RULES "(:) ++" forall x xs ys . (x:xs) ++ ys = x : (xs ++ ys) #-}
{-# RULES "[] ++"  forall xs      . [] ++ xs     = xs #-}

-- has preconditon
{-# RULES "rep-abs-fusion" forall h . repH (absH h) = h #-}





