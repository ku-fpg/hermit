module Main where

import Data.Function(fix)

data Expr = Val Int | Add Expr Expr | Throw | Catch Expr Expr

type Mint = Maybe Int

eval :: Expr -> Mint
eval (Val n)     = Just n
eval Throw       = Nothing
eval (Catch x y) = case eval x of
                       Nothing -> eval y
                       Just n  -> Just n
eval (Add x y)   = case eval x of
                       Nothing -> Nothing
                       Just m  -> case eval y of
                                    Nothing -> Nothing
                                    Just n  -> Just (m + n)

unwrap :: (Expr -> Mint) -> Expr -> (Int -> Mint) -> Mint -> Mint
unwrap g e s f = case g e of
                   Nothing -> f
                   Just n  -> s n

wrap :: (Expr -> (Int -> Mint) -> Mint -> Mint) -> Expr -> Mint
wrap h e = h e Just Nothing

{-# RULES "ww" forall f . fix f = wrap (fix (unwrap . f . wrap)) #-}

main :: IO ()
main = print (eval $ Val 5)
