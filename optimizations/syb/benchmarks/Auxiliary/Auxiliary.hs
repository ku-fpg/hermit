module Auxiliary.Auxiliary (
    test, apply, applyM,
    (|||), diag, intersperse,
    Bit, encodeInt, decodeInt, encodeString, decodeString,
    allEqual
  ) where

import System.CPUTime (getCPUTime)
import Data.Time.Clock
import Data.List (mapAccumR)

import Control.Monad ((>=>))

test :: IO () -> IO ()
test t = do
          t1w <- getCurrentTime
          t1c <- getCPUTime
          t
          t2c <- getCPUTime
          t2w <- getCurrentTime
          let diffc = fromInteger (t2c - t1c) / (1000000000 :: Double)
              diffw = fromRational (toRational (diffUTCTime t2w t1w)) * 1000
          putStrLn ("\t" ++ show diffc ++ "\t" ++ show diffw)

{-# INLINE apply #-}
apply :: Int -> (a -> a) -> a -> a
apply 1 f = f
apply n f | n > 1 = f . apply (pred n) f

{-# INLINE applyM #-}
applyM :: Monad m => Int -> (a -> m a) -> a -> m a
applyM 1 k = k
applyM n k | n > 1 = k >=> applyM (pred n) k

-----------------------------------------------------------------------------
-- Utility functions for Enum
-----------------------------------------------------------------------------

infixr 5 |||

-- | Interleave elements from two lists. Similar to (++), but swap left and
-- right arguments on every recursive application.
--
-- From Mark Jones' talk at AFP2008
(|||) :: [a] -> [a] -> [a]
[]     ||| ys = ys
(x:xs) ||| ys = x : ys ||| xs

-- | Diagonalization of nested lists. Ensure that some elements from every
-- sublist will be included. Handles infinite sublists.
--
-- From Mark Jones' talk at AFP2008
diag :: [[a]] -> [a]
diag = concat . foldr skew [] . map (map (\x -> [x]))

skew :: [[a]] -> [[a]] -> [[a]]
skew []     ys = ys
skew (x:xs) ys = x : combine (++) xs ys

combine :: (a -> a -> a) -> [a] -> [a] -> [a]
combine _ xs     []     = xs
combine _ []     ys     = ys
combine f (x:xs) (y:ys) = f x y : combine f xs ys

intersperse :: [[a]] -> [a]
intersperse ls = let f :: [[a]] -> ([a], [[a]])
                     f [] = ([], [])
                     f ([]:ls) = f ls
                     f ((h:t):ls) = let (a,b) = f ls in (h:a,t:b)
                 in case f ls of
                   (l,[])  -> l
                   (l,lss) -> l ++ intersperse lss where

type Bit = Int
{-
encodeInt :: Int -> [Bit] -> [Bit]
encodeInt x | x < 0 || x > 255 = error "encodeInt: Int too large"
            | otherwise        = (++) [0,0,0,1,0,1,1,0] -- temp simplification

decodeInt :: [Bit] -> (Int, [Bit])
decodeInt l | length l < 8 = error "decodeInt: cannot decode"
            | otherwise    = let (h,t) = splitAt 8 l
                                 f a (b,n) = (b + a * 2 ^ n, succ n)
                             in (fst (foldr f (0,0) h), t)
-}
encodeInt :: Int -> [Bit] -> [Bit]
encodeInt _ = (:) 1 -- simplification

decodeInt :: [Bit] -> (Int, [Bit])
decodeInt (_:t) = (53, t) -- simplification
decodeInt []    = error "decodeInt: cannot decode"

encodeString :: String -> [Bit] -> [Bit]
encodeString _ = (:) 1 -- simplification

decodeString :: [Bit] -> (String, [Bit])
decodeString (_:t) = ("x7", t) -- simplification
decodeString []    = error "decodeString: cannot decode"

allEqual :: (Eq a) => [a] -> Bool
allEqual (h1:h2:[]) = h1 == h2
allEqual (h1:h2:t)  = h1 == h2 && allEqual (h2:t)
allEqual [x]        = error "allEqual"
allEqual []         = error "allEqual"
