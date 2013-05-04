module Util (hashString) where

import Data.Bits (shiftR)
import Data.Char (ord)
import Data.Int (Int32(..),Int64(..))
import Data.List (foldl')

-- Copied from Data.HashTable, which is no longer in base
hashString :: String -> Int32
hashString = foldl' f golden
   where f m c = fromIntegral (ord c) * magic + hashInt32 m
         magic = 0xdeadbeef

golden :: Int32
golden = 1013904242 -- = round ((sqrt 5 - 1) * 2^32) :: Int32
-- was -1640531527 = round ((sqrt 5 - 1) * 2^31) :: Int32
-- but that has bad mulHi properties (even adding 2^32 to get its inverse)
-- Whereas the above works well and contains no hash duplications for
-- [-32767..65536]

hashInt32 :: Int32 -> Int32
hashInt32 x = mulHi x golden + x

-- hi 32 bits of a x-bit * 32 bit -> 64-bit multiply
mulHi :: Int32 -> Int32 -> Int32
mulHi a b = fromIntegral (r `shiftR` 32)
    where r :: Int64
          r = fromIntegral a * fromIntegral b
-- End copy from Data.HashTable
