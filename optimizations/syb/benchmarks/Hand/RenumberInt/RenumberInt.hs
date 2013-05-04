module Hand.RenumberInt.RenumberInt where

import Auxiliary.Tree
import Auxiliary.Logic
import Control.Monad.State

{-# INLINE getUnique #-}
getUnique :: State Int Int
getUnique = do
    u <- get
    modify (+1)
    return u

renumberInt :: Tree Int -> State Int (Tree Int)
renumberInt Leaf         = return Leaf
renumberInt (Bin _v l r)       = do
    v' <- getUnique
    l' <- renumberInt l
    r' <- renumberInt r
    return $ Bin v' l' r'

renumberIntLogic :: Logic -> State Int Logic
renumberIntLogic (Var s _i) = do
    i' <- getUnique
    return $ Var s i'
renumberIntLogic T = return T
renumberIntLogic F = return F
renumberIntLogic (Not l) = do
    l' <- renumberIntLogic l
    return $ Not l'
renumberIntLogic (Impl l r) = do
    l' <- renumberIntLogic l
    r' <- renumberIntLogic r
    return $ Impl l' r'
renumberIntLogic (Equiv l r) = do
    l' <- renumberIntLogic l
    r' <- renumberIntLogic r
    return $ Equiv l' r'
renumberIntLogic (Conj l r) = do
    l' <- renumberIntLogic l
    r' <- renumberIntLogic r
    return $ Conj l' r'
renumberIntLogic (Disj l r) = do
    l' <- renumberIntLogic l
    r' <- renumberIntLogic r
    return $ Disj l' r'
