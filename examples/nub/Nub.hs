import Criterion.Main

import qualified Data.Set as Set
import Data.Set (Set)

data R = R [Int] (Set Int)

repR :: [Int] -> R
repR xs = R xs Set.empty

absR :: R -> [Int]
absR (R xs ex) = [ x | x <- xs
                     , not (x `Set.member` ex)
                 ]

nub :: [Int] -> [Int]
nub [] = []
nub (x:xs) = x : nub (filter (\y -> x /= y) xs)

--main = print (nub [ x | n <- [1..1000], x <- [1..n] ])
main = defaultMain
        [ bench (show sz) $ nf nub [ x | n <- [1..sz], x <- [1..n] ]
        | sz <- take 2 [100,200..]
        ]
