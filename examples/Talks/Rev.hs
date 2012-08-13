module Main where

import HList
import Data.Function (fix)

unwrap :: ([a] -> [a]) -> ([a] -> [a] -> [a])
unwrap f = repH . f

wrap :: ([a] -> [a] -> [a]) -> ([a] -> [a])
wrap g = absH . g

{-# RULES "ww" forall f . fix f = wrap (fix (unwrap . f . wrap)) #-}

-- rev :: [a] -> [a]
rev []     = []
rev (x:xs) = rev xs ++ [x]

main :: IO ()
main = putStrLn $ "Successfully reversed a list of " ++ show (length $ rev [1..15000]) ++ " elements."

