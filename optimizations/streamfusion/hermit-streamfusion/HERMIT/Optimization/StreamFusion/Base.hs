{-# LANGUAGE ExistentialQuantification, BangPatterns #-}
module HERMIT.Optimization.StreamFusion.Base
    ( Stream(..)
    , Step(..)
    , SPEC(..)
    , stream
    , unstream
    , fixStep
    ) where

import GHC.Exts( SpecConstrAnnotation(..) )

{-# INLINE fixStep #-}
fixStep :: forall a b s. a -> Step b s -> Step b (a,s)
fixStep _ Done        = Done
fixStep a (Skip s)    = Skip (a,s)
fixStep a (Yield b s) = Yield b (a,s)

data Stream a = forall s. Stream (s -> Step a s) s
data Step a s = Done | Skip s | Yield a s

data SPEC = SPEC | SPEC2
{-# ANN type SPEC ForceSpecConstr #-}

{-# INLINE [0] stream #-}
stream :: [a] -> Stream a
stream xs = Stream uncons xs
    where uncons :: [a] -> Step a [a]
          uncons []     = Done
          uncons (x:xs) = Yield x xs
          {-# INLINE uncons #-}

{-# INLINE [0] unstream #-}
unstream :: Stream a -> [a]
unstream (Stream n s) = go SPEC s
    where go !sPEC s = case n s of
                        Done       -> []
                        Skip s'    -> go sPEC s'
                        Yield x s' -> x : go sPEC s'

{-# RULES "unstream/stream" forall xs. unstream (stream xs) = xs #-}
{-# RULES "stream/unstream" forall s.  stream (unstream s)  = s  #-}
