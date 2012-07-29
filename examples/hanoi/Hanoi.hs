module Main where

import Criterion.Main

import Control.Monad (forM_)

import Data.Function (fix)

type Nat = Int

main :: IO ()
main = do
    forM_ [0..20] $ \i -> do
        let h = hanoi i A B C
            h' = hanoi' i A B C
            h'' = wrap (unwrap hanoi) i A B C
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
    where (u,v,w) = worker (n-2) a b c

          worker :: Nat -> Peg -> Peg -> Peg -> (Moves, Moves, Moves)
          worker 0 _ _ _ = ([],[],[])
          worker 1 a b c = ([(a,b)], [(b,c)], [(c,a)])
          worker n a b c =
                let (u,v,w) = worker (n-2) a b c
                in (u ++ [(a,c)] ++ v ++ [(a,b)] ++ w ++ [(c,b)] ++ u
                   ,v ++ [(b,a)] ++ w ++ [(b,c)] ++ u ++ [(a,c)] ++ v
                   ,w ++ [(c,b)] ++ u ++ [(c,a)] ++ v ++ [(b,a)] ++ w)

unwrap :: (Nat -> Peg -> Peg -> Peg -> Moves)
       -> (Nat -> Peg -> Peg -> Peg -> (Moves, Moves, Moves))
unwrap f n a b c = (f n a b c, f n b c a, f n c a b)

wrap :: (Nat -> Peg -> Peg -> Peg -> (Moves, Moves, Moves))
     -> (Nat -> Peg -> Peg -> Peg -> Moves)
wrap _ 0 _ _ _ = []
wrap _ 1 a b _ = [(a,b)]
wrap f n a b c = let (u,v,w) = f (n-2) a b c
                 in u ++ [(a,c)] ++ v ++ [(a,b)] ++ w ++ [(c,b)] ++ u
