module HList
       ( repH
       , absH
       ) where

{-# INLINE repH #-}
repH :: [a] -> [a] -> [a]
repH xs = (xs ++)

{-# INLINE absH #-}
absH :: ([a] -> [a]) -> [a]
absH f = f []

{-# RULES "repH ++" forall xs ys   . repH (xs ++ ys) = repH xs . repH ys #-}

{-# RULES "(:) ++" forall x xs ys . (x:xs) ++ ys = x : (xs ++ ys) #-}
{-# RULES "[] ++"  forall xs      . [] ++ xs     = xs #-}

-- has preconditon
{-# RULES "rep-abs-fusion" forall h . repH (absH h) = h #-}



