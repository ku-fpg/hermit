data Foo = Bar Int Float | Baz String deriving (Show)

main = do
    print fa
    print fc

{-# NOINLINE bar #-}
bar = Bar 5 2.1

{-# NOINLINE fa #-}
fa = let x = Bar 3 5.4
     in "prefix " ++ show x

-- to test let-float-app (including alphaLet)
{-# NOINLINE fb #-}
fb = let x = Bar 4 6.7 in \z -> (x,z)
{-# NOINLINE x #-}
x = 2
{-# NOINLINE fc #-}
fc = fb (40 + x)
