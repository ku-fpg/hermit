import Criterion.Main

-- so we can fix-intro
import Data.Function (fix)

import Prelude hiding (,)
import GHC.Tuple

main :: IO ()
main = defaultMain
        [ bench "35" $ whnf fib 35
        ]

{-# RULES "ww" forall f . fix f = wrap (fix (unwrap . f . wrap)) #-}
{-# RULES "inline-fix" forall f . fix f = let work = f work in work #-}
{-# RULES "precondition" forall w . wrap (unwrap w) = w #-}

-- beginning of neil's derivation
fib :: Nat -> Nat
fib Zero = Zero
fib (Succ Zero) = Succ Zero
fib (Succ (Succ n)) = fib (Succ n) + fib n

-- we need a better way for when we need to case on Nat
data Nat = Zero | Succ Nat

instance Num Nat where
    n1 + Zero = n1
    n1 + (Succ n2) = Succ (n1 + n2)
    fromInteger 0 = Zero
    fromInteger i = Succ (fromInteger (i-1))

{-# INLINE wrap #-}
wrap :: (Nat -> (Nat, Nat)) -> Nat -> Nat
wrap h = fst . h

{-# INLINE unwrap #-}
unwrap :: (Nat -> Nat) -> Nat -> (Nat, Nat)
unwrap h n = (h n, h (Succ n))

{- todo?:
    others to convert this to definiton above
fib :: Nat -> Nat
fib n = if n < 2 then 1 else fib(n-1) + fib(n-2)
-}

