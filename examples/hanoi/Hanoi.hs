module Main where

import Criterion.Main

import HanoiPrelude

import Control.Monad (forM_)

main :: IO ()
main = do
    forM_ [0..20] $ \i -> do
        let h = hanoi i A B C
            h' = hanoi' i A B C
        if h == h'
        then putStrLn $ show i ++ " good."
        else do print h
                print h'

--       defaultMain
--        [ bench "4" $ whnf hanoi 4
--        ]

{-# RULES "ww" forall work . fix work = wrap (fix (unwrap . work . wrap)) #-}
{-# RULES "inline-fix" forall f . fix f = let work = f work in work #-}

data Peg = A | B | C deriving (Show, Eq)
type Moves = [(Peg,Peg)]

-- this is a candidate for tupling
hanoi :: Nat -> Peg -> Peg -> Peg -> Moves
hanoi 0 _ _ _ = []
hanoi n a b c = hanoi (n-1) a c b ++ [(a,b)] ++ hanoi (n-1) c b a

-- this is the goal
hanoi' 0 _ _ _ = []
hanoi' 1 a b _ = [(a,b)]
hanoi' n a b c = u ++ [(a,c)] ++ v ++ [(a,b)] ++ w ++ [(c,b)] ++ u
    where (u,v,w) = worker (n-2)
          worker :: Nat -> (Moves, Moves, Moves)
          worker 0 = ([],[],[])
          worker 1 = ([(a,b)], [(b,c)], [(c,a)])
          worker n = let (u,v,w) = worker (n-2)
                     in (u ++ [(a,c)] ++ v ++ [(a,b)] ++ w ++ [(c,b)] ++ u
                        ,v ++ [(b,a)] ++ w ++ [(b,c)] ++ u ++ [(a,c)] ++ v
                        ,w ++ [(c,b)] ++ u ++ [(c,a)] ++ v ++ [(b,a)] ++ w)
