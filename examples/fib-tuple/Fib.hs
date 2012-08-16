{-# LANGUAGE TemplateHaskell #-}
-- for criterion
import Criterion.Main
import Control.DeepSeq.TH

-- so we can fix-intro
import Data.Function (fix)

-- so we can let-tuple
import GHC.Tuple

import Prelude hiding ((+))

data Nat = Z | S Nat

{-# RULES "ww" forall f . fix f = wrap (fix (unwrap . f . wrap)) #-}
{-# RULES "precondition" forall w . wrap (unwrap w) = w #-}

(+) :: Nat -> Nat -> Nat
Z      + n = n
(S n') + n = S (n' + n)

fromInt :: Int -> Nat
fromInt 0 = Z
fromInt i | i < 0 = error "fromInt negative"
          | otherwise = S (fromInt (i-1))

-- original fib definition
fib :: Nat -> Nat
fib Z = Z
fib (S Z) = S Z
fib (S (S n)) = fib (S n) + fib n

-- goal:
-- fib' = fst work
--   where work Z = (Z, S Z)
--         work (S n) = let (x,y) = work n
--                         in (y,x+y)

wrap :: (Nat -> (Nat, Nat)) -> Nat -> Nat
wrap h = fst . h

unwrap :: (Nat -> Nat) -> Nat -> (Nat, Nat)
unwrap h n = (h n, h (S n))

-- for criterion
deriveNFData ''Nat

main :: IO ()
main = defaultMain
        [ bench "15" $ nf fib (fromInt 15)
        , bench "30" $ nf fib (fromInt 30)
        ]
