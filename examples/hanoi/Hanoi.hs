{-# LANGUAGE CPP #-}
module Main where

-- import Criterion.Main

import Control.Monad (forM_)

data Nat = Z | S Nat

toInt :: Nat -> Int
toInt Z = 0
toInt (S m) = 1 + toInt m

fromInt :: Int -> Nat
fromInt 0 = Z
fromInt i = S (fromInt (i-1))

instance Show Nat where
    show = show . toInt

main :: IO ()
main = do
    forM_ [0..20] $ \i -> do
        let h = hanoi (fromInt i) A B C
            h' = hanoi' (fromInt i) A B C
            h'' = wrap (unwrap hanoi) (fromInt i) A B C
        if h == h'
        then do putStrLn $ show i ++ " good."
                if h == h''
                then do putStrLn $ show i ++ " wrap/unwrap good."
                else do print h
                        print h''
        else do print h
                print h'

--       defaultMain
--        [ bench "4" $ whnf hanoi 4
--        ]

{-# RULES "++ []" forall l. l ++ [] = l #-}
{-# RULES "[] ++" forall l. [] ++ l = l #-}

data Peg = A | B | C deriving (Show, Eq)
type Moves = [(Peg,Peg)]

-- this is a candidate for tupling
hanoi :: Nat -> Peg -> Peg -> Peg -> Moves
hanoi Z     _ _ _ = []
hanoi (S n) d b c = hanoi n d c b ++ [(d,b)] ++ hanoi n c b d

-- this is the goal
hanoi' Z         _ _ _ = []
hanoi' (S Z)     d b _ = [(d,b)]
hanoi' (S (S n)) d b c = u ++ [(d,c)] ++ v ++ [(d,b)] ++ w ++ [(c,b)] ++ u
    where (u,v,w) = worker n d b c

          worker :: Nat -> Peg -> Peg -> Peg -> (Moves, Moves, Moves)
          worker Z         _ _ _ = ([],[],[])
          worker (S Z)     d b c = ([(d,b)], [(b,c)], [(c,d)])
          worker (S (S n)) d b c =
                let (u,v,w) = worker n d b c
                in (u ++ [(d,c)] ++ v ++ [(d,b)] ++ w ++ [(c,b)] ++ u
                   ,v ++ [(b,d)] ++ w ++ [(b,c)] ++ u ++ [(d,c)] ++ v
                   ,w ++ [(c,b)] ++ u ++ [(c,d)] ++ v ++ [(b,d)] ++ w)

unwrap :: (Nat -> Peg -> Peg -> Peg -> Moves)
       -> (Nat -> Peg -> Peg -> Peg -> (Moves, Moves, Moves))
unwrap f n d b c = (f n d b c, f n b c d, f n c d b)

wrap :: (Nat -> Peg -> Peg -> Peg -> (Moves, Moves, Moves))
     -> (Nat -> Peg -> Peg -> Peg -> Moves)
wrap _ Z         _ _ _ = []
wrap _ (S Z)     d b _ = [(d,b)]
wrap f (S (S n)) d b c = let (u,v,w) = f n d b c
                         in u ++ [(d,c)] ++ v ++ [(d,b)] ++ w ++ [(c,b)] ++ u
