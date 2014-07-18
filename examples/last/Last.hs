{-# LANGUAGE CPP #-}
module Main where

import Prelude hiding (last)

-------------------------------------------------

unwrap         :: ([a] -> a) -> a -> [a] -> a
unwrap f a as  = f (a:as)

wrap           :: (a -> [a] -> a) -> [a] -> a
wrap f []      = undefined
wrap f (a:as)  = f a as

last           :: [a] -> a
last []        = undefined
last [a]       = a
last (_:a:as)  = last (a:as)

main :: IO ()
main = print (last "hello")

-------------------------------------------------
