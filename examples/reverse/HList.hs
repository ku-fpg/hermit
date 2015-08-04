module HList
       ( H
       , repH
       , absH
       ) where

type H a = [a] -> [a]

-- {-# INLINE repH #-}
repH :: [a] -> H a
repH xs = (xs ++)

-- {-# INLINE absH #-}
absH :: H a -> [a]
absH f = f []

-- -- Should be in a "List" module
-- {-# RULES "++ []"  forall xs .  xs ++ [] = xs #-}
-- {-# RULES "++ strict"           (++) undefined = undefined #-}

-- -- The "Algebra" for repH
-- {-# RULES "repH ++" forall xs ys   . repH (xs ++ ys) = repH xs . repH ys #-}
-- {-# RULES "repH []"                  repH [] = id                        #-}
-- {-# RULES "repH (:)" forall x xs   . repH (x:xs) = ((:) x) . repH xs     #-}
