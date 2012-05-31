{-# RULES "appendNil" forall xs . xs ++ [] = xs #-}

{-# NOINLINE foo #-}
foo = [1] ++ []

main = print foo
