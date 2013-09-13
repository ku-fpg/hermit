module Main where

import Data.Function (fix)
import GHC.Err (undefined)

data A = A
data B = B

f :: A -> B
f A = B

g :: A -> A
g A = A

h :: B -> B
h B = B

prog :: B
prog = f (fix g)

main :: IO ()
main = return ()
