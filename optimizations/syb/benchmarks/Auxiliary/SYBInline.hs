{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE FlexibleInstances     #-}

module Auxiliary.SYBInline where

import Auxiliary.Tree (Tree(..))
import Auxiliary.Logic (Logic(..))
import Data.Generics


-- Data instance for Tree
instance Data (Tree Int) where
  gfoldl = gfoldlTree
  
  toConstr Leaf        = leafConstr
  toConstr (Bin _ _ _) = binConstr
  
  dataTypeOf _ = treeDataType
  
  dataCast1 f = gcast1 f
  
  gunfold = gunfoldTree
  
  gmapQ = gmapQTree
  gmapT = gmapTTree

{-# INLINE gfoldlTree #-}
gfoldlTree :: (forall d b. (Data d) => c (d -> b) -> d -> c b)
           -> (forall g. g -> c g)
           -> Tree Int -> c (Tree Int)
gfoldlTree k z Leaf        = z Leaf
gfoldlTree k z (Bin x l r) = z Bin `k` x `k` l `k` r

{-# INLINE gunfoldTree #-}
gunfoldTree :: (forall b r. (Data b) => c (b -> r) -> c r)
            -> (forall r. r -> c r)
            -> Constr -> c (Tree Int)
gunfoldTree k z c = case constrIndex c of
                      1 ->          z Leaf
                      2 -> k (k (k (z Bin)))
                      _ -> error "gunfold"
  
{-# INLINE gmapQTree #-}
{- RULES 
"gmapQTree/Leaf" forall (f :: (forall d. Data d => d -> u)). gmapQTree f Leaf = [] 
"gmapQTree/Bin" forall (f :: (forall d. Data d => d -> u)) x l r. gmapQTree f (Bin x l r) = [f x, f l, f r] 
  #-}
gmapQTree :: (forall d. Data d => d -> u) -> Tree Int -> [u]
gmapQTree f Leaf = []
gmapQTree f (Bin x l r) = [f x, f l, f r]

{-# INLINE gmapTTree #-}
gmapTTree :: (forall b. Data b => b -> b) -> Tree Int -> Tree Int
gmapTTree _ Leaf        = Leaf
gmapTTree f (Bin x l r) = Bin (f x) (f l) (f r)

{-# INLINE leafConstr #-}
{-# INLINE binConstr  #-}
leafConstr, binConstr :: Constr
leafConstr = mkConstr treeDataType "Leaf" [] Prefix
binConstr  = mkConstr treeDataType "Bin"  [] Prefix

{-# INLINE treeDataType #-}
treeDataType :: DataType
treeDataType = mkDataType "Auxiliary.SYBInline.Tree" [leafConstr,binConstr]


--------------------------------------------------------------------------------
-- Data instance for Logic
instance Data Logic where
  gfoldl = gfoldlLogic
  
  toConstr (Var _)      = varConstr
  toConstr T            = tConstr
  toConstr F            = fConstr
  toConstr (Not _)      = notConstr
  toConstr (Impl _ _)   = implConstr
  toConstr (Equiv _ _)  = equivConstr
  toConstr (Conj _ _)   = conjConstr
  toConstr (Disj _ _)   = disjConstr
  
  dataTypeOf _ = logicDataType
  
  gunfold = gunfoldLogic
  
  gmapQ = gmapQLogic
  gmapT = gmapTLogic


{-# INLINE gfoldlLogic #-}
gfoldlLogic :: (forall d b. (Data d) => c (d -> b) -> d -> c b)
            -> (forall g. g -> c g)
            -> Logic -> c Logic
gfoldlLogic k z (Var x)     = z Var   `k` x
gfoldlLogic k z T           = z T
gfoldlLogic k z F           = z F
gfoldlLogic k z (Not l)     = z Not   `k` l
gfoldlLogic k z (Impl p q)  = z Impl  `k` p `k` q
gfoldlLogic k z (Equiv p q) = z Equiv `k` p `k` q
gfoldlLogic k z (Conj p q)  = z Conj  `k` p `k` q
gfoldlLogic k z (Disj p q)  = z Disj  `k` p `k` q

{-# INLINE gunfoldLogic #-}
gunfoldLogic :: (forall b r. (Data b) => c (b -> r) -> c r)
             -> (forall r. r -> c r)
             -> Constr -> c Logic
gunfoldLogic k z c = case constrIndex c of
                      1 -> k (   z Var)
                      2 ->       z T
                      3 ->       z F
                      4 -> k (   z Not)
                      5 -> k (k (z Impl))
                      6 -> k (k (z Equiv))
                      7 -> k (k (z Conj))
                      8 -> k (k (z Disj))
                      _ -> error "gunfold"
  
{-# INLINE gmapQLogic #-}
gmapQLogic :: (forall d. Data d => d -> u) -> Logic -> [u]
gmapQLogic f (Var x)     = [f x]
gmapQLogic f T           = []
gmapQLogic f F           = []
gmapQLogic f (Not x)     = [f x]
gmapQLogic f (Impl p q)  = [f p, f q]
gmapQLogic f (Equiv p q) = [f p, f q]
gmapQLogic f (Conj p q)  = [f p, f q]
gmapQLogic f (Disj p q)  = [f p, f q]

{-# INLINE gmapTLogic #-}
gmapTLogic :: (forall b. Data b => b -> b) -> Logic -> Logic
gmapTLogic f (Var x)     = Var (f x)
gmapTLogic _ T           = T
gmapTLogic _ F           = F
gmapTLogic f (Not x)     = Not (f x)
gmapTLogic f (Impl p q)  = Impl (f p) (f q)
gmapTLogic f (Equiv p q) = Equiv (f p) (f q)
gmapTLogic f (Conj p q)  = Conj (f p) (f q)
gmapTLogic f (Disj p q)  = Disj (f p) (f q)

{-# INLINE varConstr   #-}
{-# INLINE tConstr     #-}
{-# INLINE fConstr     #-}
{-# INLINE notConstr   #-}
{-# INLINE implConstr  #-}
{-# INLINE equivConstr #-}
{-# INLINE conjConstr  #-}
{-# INLINE disjConstr  #-}
varConstr, tConstr, fConstr, notConstr, implConstr, 
  equivConstr, conjConstr, disjConstr :: Constr
varConstr   = mkConstr logicDataType "Var"    [] Prefix
tConstr     = mkConstr logicDataType "T"      [] Prefix
fConstr     = mkConstr logicDataType "F"      [] Prefix
notConstr   = mkConstr logicDataType "Not"    [] Prefix
implConstr  = mkConstr logicDataType "Impl"   [] Prefix
equivConstr = mkConstr logicDataType "Equiv"  [] Prefix
conjConstr  = mkConstr logicDataType "Conj"   [] Prefix
disjConstr  = mkConstr logicDataType "Disj"   [] Prefix

{-# INLINE logicDataType  #-}
logicDataType :: DataType
logicDataType = mkDataType "Auxiliary.SYBInline.Logic" 
                  [varConstr, tConstr, fConstr, notConstr, implConstr
                  , equivConstr, conjConstr, disjConstr]
