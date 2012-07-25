{-# LANGUAGE TemplateHaskell #-}
-- for criterion
import Criterion.Main
import Control.DeepSeq.TH

-- so we can fix-intro
import Data.Function (fix)

-- so we can let-tuple
import GHC.Tuple

data Nat = Zero | Succ Nat

{-# RULES "ww" forall f . fix f = wrap (fix (unwrap . f . wrap)) #-}
{-# RULES "inline-fix" forall f . fix f = let work = f work in work #-}
{-# RULES "precondition" forall w . wrap (unwrap w) = w #-}

-- original fib definition
fib :: Nat -> Nat
fib Zero = Zero
fib (Succ Zero) = Succ Zero
fib (Succ (Succ n)) = fib (Succ n) + fib n

-- goal:
-- fib' = fst work
--   where work Zero = (Zero, Succ Zero)
--         work (Succ n) = let (x,y) = work n
--                         in (y,x+y)

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

-- for criterion
deriveNFData ''Nat

main :: IO ()
main = defaultMain
        [ bench "15" $ nf fib 15
        , bench "30" $ nf fib 30
        ]
