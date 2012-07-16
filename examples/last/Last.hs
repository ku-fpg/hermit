module Main where

import Data.Function(fix)
import Prelude hiding (last)

unwrap         :: ([a] -> a) -> a -> [a] -> a
unwrap f a as  = f (a:as)

wrap           :: (a -> [a] -> a) -> [a] -> a
wrap f []      = error "wrap _ []"
wrap f (a:as)  = f a as

{-# RULES "ww" forall f . fix f = wrap (fix (unwrap . f . wrap)) #-}

-- last :: [a] -> a
last []       = error "last []"
last [a]      = a
last (_:a:as) = last (a:as)

main :: IO ()
main = print (last "hello")
