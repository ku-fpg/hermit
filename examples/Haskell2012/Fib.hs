import Criterion.Main

fib :: Int -> Int
fib n = if n < 2 then 1 else fib(n-1) + fib(n-2)

main = defaultMain
        [ bench "35" $ whnf fib 35
        ]
