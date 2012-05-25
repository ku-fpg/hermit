data Foo = Bar Int Float | Baz String deriving (Show)

main = do
    print fb
    print baz
    print fa

{-# NOINLINE bar #-}
bar = Bar 5 2.1

{-# NOINLINE foo #-}
foo x = case x of
        Bar x f -> show x
        Baz s -> s

-- how to turn off the GHC simplifier?!
{-# NOINLINE baz #-}
baz = case bar of
        Baz s -> s
        x -> show x
        _ -> ""

{-# NOINLINE fa #-}
fa = let x = Bar 3 5.1 in show x

{-# NOINLINE fb #-}
fb = foo bar
