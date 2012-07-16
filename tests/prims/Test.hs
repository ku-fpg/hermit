module Main where

main = print "Test"

------------------------ beta reduction ---------------------
beta_reduce_start :: Int
beta_reduce_start = f 1
  where
        f = \ x -> x + 2 :: Int -- is auto-inlined

beta_reduce_end :: Int
beta_reduce_end = 1 + 2

------------------------ case reduction ---------------------
data Foo a = Bar Int Float a | Baz String

case_reduce_start = case bar of
                        Bar x f a -> show x
                        Baz s -> s
    where {-# NOINLINE bar #-}
          bar = Bar 5 2.1 'a'

case_reduce_end = show (5 :: Int)

------------------------ adding and using a rule ---------------------

--{-# NOINLINE capture_me #-}
capture_me :: Int
capture_me = 99

new_rule_start = capture_me

new_rule_end = 99 :: Int

------------------------ fold -----------------------------

double :: Int -> Int
double x = x + x

fold_start :: Int
fold_start = 5 + 5 + 6

fold_end = double 5 + 6
