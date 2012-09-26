{-# LANGUAGE MagicHash #-}

import GHC.Exts
import Data.Function(fix)
import Prelude hiding ((*),(-))

fac :: Int -> Int
fac 0 = 1
fac n = n * fac (n -1)

unwrap :: (Int -> Int) -> Int# -> Int#
unwrap h x = case h (I# x) of
               I# y -> y

wrap :: (Int# -> Int#) -> Int -> Int
wrap h (I# x) = I# (h x)

{-# RULES "ww"     forall f. fix f = wrap (fix (unwrap . f . wrap)) #-}

main :: IO ()
main = print (fac 50)


(*) :: Int -> Int -> Int
(I# x) * (I# y) = I# (x *# y)

(-) :: Int -> Int -> Int
(I# x) - (I# y) = I# (x -# y)
