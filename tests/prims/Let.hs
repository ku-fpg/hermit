data Foo = Bar Int Float | Baz String deriving (Show)

main = do
    print fa

{-# NOINLINE bar #-}
bar = Bar 5 2.1

{-# NOINLINE fa #-}
{-# NOINLINE x #-}
fa = let x = Bar 3 5.4
     in "prefix " ++ show x
