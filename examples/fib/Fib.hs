import Criterion.Main

import FibPrelude

main :: IO ()
main = defaultMain
        [ bench "35" $ whnf fib 35
        ]

{-# RULES "ww" forall work . fix work = wrap (fix (unwrap . work . wrap)) #-}

-- beginning of neil's derivation
fib :: Nat -> Nat
fib 0 = 1
fib 1 = 1
fib n = fib (n-1) + fib (n-2)

-- status: apply-rule ww doesn't work

{- todo?:
    if-to-case:
        if c then e1 else e2 ==> case c of
                                    True -> e1
                                    False -> e2
    case-on-type?
    others to convert this to definiton above
fib :: Nat -> Nat
fib n = if n < 2 then 1 else fib(n-1) + fib(n-2)
-}

