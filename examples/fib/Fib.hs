import Criterion.Main

import FibPrelude

main :: IO ()
main = defaultMain
        [ bench "35" $ whnf fib 35
        ]

{-# RULES "ww" forall work . fix work = wrap (fix (unwrap . work . wrap)) #-}
{-# RULES "inline-fix" forall f . fix f = let work = f work in work #-}

-- beginning of neil's derivation
fib :: Nat -> Nat
fib Zero = Zero
fib (Succ Zero) = Succ Zero
fib (Succ (Succ n)) = fib (Succ n) + fib n

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

