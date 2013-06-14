{-# LANGUAGE ExistentialQuantification #-}
module HERMIT.Optimization.StreamFusion.List
    ( Stream(..)
    , Step(..)
    , stream
    , unstream
    , mapS
    , foldlS
    , concatMapS
    , flatten
    , flattenS
    , fixStep
    , enumFromToS
    , filterS
    , zipS
    ) where

data Stream a = forall s. Stream (s -> Step a s) s
data Step a s = Done | Skip s | Yield a s

{-# NOINLINE stream #-}
stream :: [a] -> Stream a
stream xs = Stream uncons xs
    where uncons :: [a] -> Step a [a]
          uncons []     = Done
          uncons (x:xs) = Yield x xs

unstream :: Stream a -> [a]
unstream (Stream n s) = go s
    where go s = case n s of
                    Done       -> []
                    Skip s'    -> go s'
                    Yield x s' -> x : go s'

{-# RULES "unstream/stream" [~] forall xs. unstream (stream xs) = xs #-}
{-# RULES "stream/unstream" [~] forall s.  stream (unstream s)  = s  #-}

mapS :: (a -> b) -> Stream a -> Stream b
mapS f (Stream n s) = Stream n' s
    where n' s = case n s of
                    Done       -> Done
                    Skip s'    -> Skip s'
                    Yield x s' -> Yield (f x) s'

{-# RULES "mapS" [~] forall f. map f = unstream . mapS f . stream #-}

foldlS :: (b -> a -> b) -> b -> Stream a -> b
foldlS f z (Stream n s) = go z s
    where go z s = case n s of
                    Done       -> z
                    Skip s'    -> go z s'
                    Yield x s' -> go (f z x) s'

{-# RULES "foldlS" [~] forall f z. foldl f z = foldlS f z . stream #-}

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

flatten :: forall a b s. (a -> s) -> (s -> Step b s) -> [a] -> [b]
flatten mk gFlatten = unstream . flattenS mk gFlatten . stream

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

{-# INLINE fixStep #-}
fixStep :: forall a b s. a -> Step b s -> Step b (a,s)
fixStep _ Done        = Done
fixStep a (Skip s)    = Skip (a,s)
fixStep a (Yield b s) = Yield b (a,s)

{-# RULES "concatMapS" [~] forall f. concatMap f = unstream . concatMapS (stream . f) . stream #-}

enumFromToS :: Enum a => a -> a -> Stream a
enumFromToS l h = Stream gEnum sEnum
    where {-# INLINE gEnum #-}
          gEnum s | s > fromEnum h = Done
                  | otherwise      = Yield (toEnum s) (succ s)
          sEnum = fromEnum l
          {-# INLINE sEnum #-}

{-# RULES "enumFromToS" [~] forall l h. enumFromTo l h = unstream (enumFromToS l h) #-}

filterS :: (a -> Bool) -> Stream a -> Stream a
filterS p (Stream n s) = Stream n' s
    where n' s = case n s of
                    Done -> Done
                    Skip s' -> Skip s'
                    Yield x s' | p x -> Yield x s'
                               | otherwise -> Skip s'

{-# RULES "filterS" [~] forall p. filter p = unstream . filterS p . stream #-}

zipS :: Stream a -> Stream b -> Stream (a,b)
zipS (Stream na sa) (Stream nb sb) = Stream n (sa, sb, Nothing)
    where n (sa, sb, Nothing) = case na sa of
                                    Done -> Done
                                    Skip sa' -> Skip (sa', sb, Nothing)
                                    Yield a sa' -> Skip (sa', sb, Just a)
          n (sa, sb, Just a) = case nb sb of
                                    Done -> Done
                                    Skip sb' -> Skip (sa, sb', Just a)
                                    Yield b sb' -> Yield (a,b) (sa, sb', Nothing)

{-# RULES "zipS" [~] forall xs ys. zip xs ys = unstream (zipS (stream xs) (stream ys)) #-}

