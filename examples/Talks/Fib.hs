module Main where

fib :: Int -> Int
fib n = if n < 2
         then 1
         else fib (n-1) + fib (n-2)

main :: IO ()
main = putStrLn $ "fib 30 = " ++ show (fib 30)
