module HList
    ( H
    , repH
    , absH
    , myAppend
    ) where

type H a = [a] -> [a]

{-# INLINABLE repH #-}
repH :: [a] -> H a
repH xs = (xs ++)

{-# INLINABLE absH #-}
absH :: H a -> [a]
absH f = f []

-- Because we can't get unfolding for ++
myAppend :: [a] -> [a] -> [a]
myAppend []     ys = ys
myAppend (x:xs) ys = x : myAppend xs ys
{-# RULES "appendFix" [~] (++) = myAppend #-}

-- Algebra for repH
{-# RULES "repH []"  [~]               repH [] = id #-}
{-# RULES "repH (:)" [~] forall x xs.  repH (x:xs) = (x:) . repH xs #-}
{-# RULES "repH ++"  [~] forall xs ys. repH (xs ++ ys) = repH xs . repH ys #-}

-- Needed because the fusion rule we generate isn't too useful yet.
{-# RULES "repH-absH-fusion" [~] forall h. repH (absH h) = h #-}
