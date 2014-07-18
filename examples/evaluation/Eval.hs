{-# LANGUAGE CPP #-}
module Main where

import Prelude hiding (abs)

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

abs :: ((Int -> Mint) -> Mint -> Mint) -> Mint
abs h = h Just Nothing

rep :: Mint -> (Int -> Mint) -> Mint -> Mint
rep mn s f = case mn of
               Nothing -> f
               Just n  -> s n

main :: IO ()
main = print (eval $ Val 5)
