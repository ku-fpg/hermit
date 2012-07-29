

collatz :: Integer -> Integer
collatz n | even n = n `div` 2
	  | odd n  = 3 * n + 1

chop :: [Integer] -> [Integer]
chop (x:xs) = x : if x == 1 then [] else chop xs

chain :: Integer -> [Integer]
chain = chop . iterate collatz

{-# RULES "map !!" forall f xs n . map f xs !! n = f (xs !! n) #-}

{-# RULES "!! [n..]" forall n x . [n..] !! x = x + n #-}

-- ww : [[Integer]] ~~> Map Int [Integer]

chains :: [[Integer]]
chains = map chain [1..]

lengths :: [Int]
lengths = map length chains

longest_chain :: Int -> Int
longest_chain n = maximum (take n lengths)

main = print $ head [ i
                    | (x,i) <- lengths `zip` [1..]
                    , x == longest_chain 1000000
                    ]
