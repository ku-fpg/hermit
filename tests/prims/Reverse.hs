import Prelude hiding (reverse)

main = print (reverse "Hello, World")

reverse []     = []
reverse (x:xs) = reverse xs ++ [x]
