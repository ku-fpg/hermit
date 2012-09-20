import Prelude hiding (sum, length, foldr)

-- so we can let-tuple
import Data.Tuple
import GHC.Tuple

{-# NOINLINE mean #-}
mean :: [Int] -> Int
mean xs = sum xs `div` length xs

sum :: [Int] -> Int
sum xs = foldr (+) 0 xs

length :: [Int] -> Int
length xs = foldr (const $ (+) 1) 0 xs

foldr f z [] = z
foldr f z (x:xs) = x `f` foldr f z xs

main :: IO ()
main = print $ mean [1..10]
