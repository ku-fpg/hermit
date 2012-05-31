module Main where
import Criterion.Main
import HERMIT

{-# RULES "ww" forall work . fix work = wrap (fix (unwrap . work . wrap)) #-}
{-# RULES "repH" forall xs . repH xs = (xs ++) #-}
{-# RULES "absH" forall f . absH f = f [] #-}
{-# RULES "repAppend" forall xs ys . repH (xs ++ ys) = repH xs . repH ys #-}
{-# RULES "repAppFusion" forall h . repH (absH h) = h #-}
-- since we can't inline ++
-- if we could, I don't think we'd need these two rules
{-# RULES "append" forall x xs ys . (x:xs) ++ ys = x : (xs ++ ys) #-}
{-# RULES "appendNil" forall xs . [] ++ xs = xs #-}

rev []     = []
rev (x:xs) = rev xs ++ [x]

--hermit :: () -> a
--hermit = undefined

f g = let x = g x in x

main = defaultMain
       [ bench (show n) $ whnf (\n -> sum $ rev [1..n]) n
       | n <- take 4 $ iterate (* 10) 1
       ]
{-
import Prelude hiding (reverse)

{-# RULES "append-assoc-left" forall xs ys zs . (xs ++ ys) ++ zs = xs ++ (ys ++ zs) #-}

main = print (reverse "Hello, World")

reverse []     = []
reverse (x:xs) = reverse xs ++ [x]

test :: [Int]
test = ([1] ++ [2]) ++ [3]


foo :: Int -> Bool -> Float -> Int
foo a b c = f (x + y + z)
  where
     {-# NOINLINE x #-}
     x = 1
     {-# NOINLINE y #-}
     y = 2
     {-# NOINLINE z #-}
     z = 3 + a
     {-# NOINLINE f #-}
     f x = x + 1

-}
