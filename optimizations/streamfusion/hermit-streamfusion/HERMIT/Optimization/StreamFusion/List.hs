{-# LANGUAGE ExistentialQuantification, BangPatterns #-}
module HERMIT.Optimization.StreamFusion.List
    ( module HERMIT.Optimization.StreamFusion.Base
    , mapS
    , foldlS
    , foldrS
    , concatMapS
    , flatten
    , flattenS
    , fixStep
    , enumFromToS
    , filterS
    , zipS
    , zipWithS
    , headS
    , appendS
    , nilS
    , consS
    , singletonS
    , tailS
    , lengthS
    ) where

import Data.List
import HERMIT.Optimization.StreamFusion.Base

{-# INLINE mapS #-}
mapS :: (a -> b) -> Stream a -> Stream b
mapS f (Stream n s) = Stream n' s
    where n' s = case n s of
                    Done       -> Done
                    Skip s'    -> Skip s'
                    Yield x s' -> Yield (f x) s'
          {-# INLINE n' #-}
{-# RULES "mapS" forall f. map f = unstream . mapS f . stream #-}

{-# INLINE foldlS #-}
foldlS :: (b -> a -> b) -> b -> Stream a -> b
foldlS f z (Stream n s) = go SPEC z s
    where go !sPEC z s = case n s of
                            Done       -> z
                            Skip s'    -> go sPEC z s'
                            Yield x s' -> go sPEC (f z x) s'
{-# RULES "foldlS" forall f z. foldl f z = foldlS f z . stream #-}

{-# INLINE foldlS' #-}
foldlS' :: (b -> a -> b) -> b -> Stream a -> b
foldlS' f z (Stream n s) = go SPEC z s
    where go !sPEC !z !s = case n s of
                            Done       -> z
                            Skip s'    -> go sPEC z s'
                            Yield x s' -> go sPEC (f z x) s'
{-# RULES "foldlS'" forall f z. foldl' f z = foldlS' f z . stream #-}

{-# INLINE foldrS #-}
foldrS :: (a -> b -> b) -> b -> Stream a -> b
foldrS f z (Stream n s) = go SPEC s
    where go !sPEC s = case n s of
                        Done       -> z
                        Skip s'    -> go sPEC s'
                        Yield x s' -> f x (go sPEC s')
{-# RULES "foldrS" forall f z. foldr f z = foldrS f z . stream #-}

{-# INLINE [0] concatMapS #-}
concatMapS :: (a -> Stream b) -> Stream a -> Stream b
concatMapS f (Stream n s) = Stream n' (s, Nothing)
    where n' (s, Nothing) = case n s of
                                Done -> Done
                                Skip s' -> Skip (s', Nothing)
                                Yield x s' -> Skip (s', Just (f x))
          n' (s, Just (Stream n'' s'')) = case n'' s'' of
                                            Done -> Skip (s, Nothing)
                                            Skip s' -> Skip (s, Just (Stream n'' s'))
                                            Yield x s' -> Yield x (s, Just (Stream n'' s'))
          {-# INLINE n' #-}
{-# RULES
"concatMapS" forall f. concatMap f = unstream . concatMapS (stream . f) . stream
"concat/concatMap" forall f xs. concat (map f xs) = concatMap f xs
  #-}
-- "concat/concatMapS" forall f. concat . unstream . mapS f = unstream . concatMapS f

{-# INLINE flatten #-}
flatten :: forall a b s. (a -> s) -> (s -> Step b s) -> [a] -> [b]
flatten mk gFlatten = unstream . flattenS mk gFlatten . stream

{-# INLINE flattenS #-}
flattenS :: forall a b s. (a -> s) -> (s -> Step b s) -> Stream a -> Stream b
flattenS mk gFlatten (Stream n s) = Stream n' sFlatten
    where n' (s, Nothing) = case n s of
                                    Done -> Done
                                    Skip s' -> Skip (s', Nothing)
                                    Yield x s' -> Skip (s', Just (mk x))
          n' (s, Just s'') = case gFlatten s'' of
                                    Done -> Skip (s, Nothing)
                                    Skip s' -> Skip (s, Just s')
                                    Yield x s' -> Yield x (s, Just s')
          {-# INLINE n' #-}
          sFlatten = (s, Nothing)
          {-# INLINE sFlatten #-}

{-# INLINE enumFromToS #-}
enumFromToS :: Enum a => a -> a -> Stream a
enumFromToS l h = Stream gEnum sEnum
    where {-# INLINE gEnum #-}
          gEnum s | s > fromEnum h = Done
                  | otherwise      = Yield (toEnum s) (s+1)
          sEnum = fromEnum l
          {-# INLINE sEnum #-}
{-# RULES "enumFromToS" forall l. enumFromTo l = unstream . enumFromToS l #-}

{-# INLINE filterS #-}
filterS :: (a -> Bool) -> Stream a -> Stream a
filterS p (Stream n s) = Stream n' s
    where n' s = case n s of
                    Done -> Done
                    Skip s' -> Skip s'
                    Yield x s' | p x -> Yield x s'
                               | otherwise -> Skip s'
{-# RULES "filterS" forall p. filter p = unstream . filterS p . stream #-}

{-# INLINE zipS #-}
zipS :: Stream a -> Stream b -> Stream (a,b)
zipS = zipWithS (,)
{-# RULES "zipS" forall xs. zip xs = unstream . zipS (stream xs) . stream #-}

{-# INLINE zipWithS #-}
zipWithS :: (a -> b -> c) -> Stream a -> Stream b -> Stream c
zipWithS f (Stream na sa) (Stream nb sb) = Stream n (sa, sb, Nothing)
    where n (sa, sb, Nothing) = case na sa of
                                    Done -> Done
                                    Skip sa' -> Skip (sa', sb, Nothing)
                                    Yield a sa' -> Skip (sa', sb, Just a)
          n (sa, sb, Just a) = case nb sb of
                                    Done -> Done
                                    Skip sb' -> Skip (sa, sb', Just a)
                                    Yield b sb' -> Yield (f a b) (sa, sb', Nothing)
          {-# INLINE n #-}
{-# RULES "zipWithS" forall f xs. zipWith f xs = unstream . zipWithS f (stream xs) . stream #-}

{-# INLINE iterateS #-}
iterateS :: (a -> a) -> a -> Stream a
iterateS f x = Stream n x
    where n x = Yield x (f x)
          {-# INLINE n #-}
{-# RULES "iterateS" forall f. iterate f = unstream . iterateS f #-}

{-# INLINE headS #-}
headS :: Stream a -> a
headS (Stream n s) = go SPEC s
    where go !sPEC s = case n s of
                        Done -> error "headS empty stream"
                        Skip s' -> go sPEC s'
                        Yield x _ -> x
{-# RULES "headS" head = headS . stream #-}

{-# INLINE appendS #-}
appendS :: Stream a -> Stream a -> Stream a
appendS (Stream n1 s1) (Stream n2 s2) = Stream n (Left s1)
    where n (Left s1) = case n1 s1 of
                            Done -> Skip (Right s2)
                            Skip s1' -> Skip (Left s1')
                            Yield x s1' -> Yield x (Left s1')
          n (Right s2) = case n2 s2 of
                            Done -> Done
                            Skip s2' -> Skip (Right s2')
                            Yield x s2' -> Yield x (Right s2')
          {-# INLINE n #-}
{-# RULES "appendS" forall xs ys. xs ++ ys = unstream (appendS (stream xs) (stream ys)) #-}

{-# INLINE nilS #-}
nilS :: Stream a
nilS = Stream (\() -> Done) ()
{-# RULES "nilS" stream [] = nilS #-}

{-# INLINE consS #-}
consS :: a -> Stream a -> Stream a
consS x (Stream n s) = Stream n' (Left s)
    where n' (Left s) = Yield x (Right s)
          n' (Right s) = case n s of
                            Done -> Done
                            Skip s' -> Skip (Right s')
                            Yield x s' -> Yield x (Right s')
          {-# INLINE n' #-}
-- Note: this RULE must never run during or after a phase where unstream
-- is inlinable, or programs will diverge.
-- {-# RULES "consS" [~0] forall x xs. (:) x xs = unstream (consS x (stream xs)) #-}
{-# RULES "consS" forall x xs. stream (x : xs) = consS x (stream xs) #-}

{-# INLINE singletonS #-}
singletonS :: a -> Stream a
singletonS x = Stream n (Just x)
    where n (Just x) = Yield x Nothing
          n Nothing  = Done
          {-# INLINE n #-}
-- {-# RULES "singletonS" forall x. consS x nilS = singletonS x #-}
{-# RULES "singletonS" forall x. (:) x [] = unstream (singletonS x) #-}

{-# INLINE tailS #-}
tailS :: Stream a -> Stream a
tailS (Stream n s) = Stream n' (Left s)
    where n' (Left s) = case n s of
                            Done -> error "tailS empty stream"
                            Skip s' -> Skip (Left s')
                            Yield _ s' -> Skip (Right s')
          n' (Right s) = case n s of
                            Done -> Done
                            Skip s' -> Skip (Right s')
                            Yield x s' -> Yield x (Right s')
          {-# INLINE n' #-}
{-# RULES "tailS" tail = unstream . tailS . stream #-}

-- TODO: foldl'
{-# INLINE lengthS #-}
lengthS :: Stream a -> Int
lengthS (Stream n s) = go SPEC 0 s
    where go !sPEC !acc s = case n s of
                                Done -> acc
                                Skip s' -> go sPEC acc s'
                                Yield _ s' -> go sPEC (acc+1) s'
{-# RULES "lengthS" length = lengthS . stream #-}
