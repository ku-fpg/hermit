{-# LANGUAGE EmptyDataDecls        #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeSynonymInstances  #-}

module Auxiliary.Deriving where

import Auxiliary.Tree (Tree(..))
import Auxiliary.Logic (Logic(..))
import Auxiliary.Nat (Nat(..))
import GHC.Generics

--------------------------------------------------------------------------------
-- Tree
--------------------------------------------------------------------------------
type Rep1Tree = U1 :+: Par1 :*: Rec1 Tree :*: Rec1 Tree

instance Generic1 Tree where
  type Rep1 Tree = Rep1Tree
  {-# INLINE [1] from1 #-}
  from1 (Bin x l r) = R1 (Par1 x :*: Rec1 l :*: Rec1 r)
  from1 Leaf        = L1 U1

  {-# INLINE [1] to1 #-}
  to1 (R1 (Par1 x :*: Rec1 l :*: Rec1 r)) = Bin x l r
  to1 (L1 U1)                             = Leaf


data Tree_
instance Datatype Tree_ where
    datatypeName _ = "Tree"
    moduleName _ = "Auxiliary.Tree"
data Tree_Leaf_
data Tree_Bin_
instance Constructor Tree_Leaf_ where
    { conName _ = "Leaf" }
instance Constructor Tree_Bin_ where
    { conName _ = "Bin" }

type Rep0Tree_ a = D1 Tree_ ((:+:) (C1 Tree_Leaf_ (S1 NoSelector U1)) 
  (C1 Tree_Bin_ ((:*:) (S1 NoSelector (Rec0 a)) ((:*:) (S1 NoSelector 
    (Rec0 (Tree a))) (S1 NoSelector (Rec0 (Tree a)))))))
instance Generic (Tree a) where
  type Rep (Tree a) = Rep0Tree_ a
  {-# INLINE [1] from #-}
  from Leaf = M1 (L1 (M1 (M1 U1)))
  from (Bin f0 f1 f2)
      = M1
          (R1 (M1 ((:*:) (M1 (K1 f0)) ((:*:) (M1 (K1 f1)) (M1 (K1 f2))))))
  {-# INLINE [1] to #-}
  to (M1 (L1 (M1 (M1 U1)))) = Leaf
  to
      (M1 (R1 (M1 ((:*:) (M1 (K1 f0)) ((:*:) (M1 (K1 f1)) (M1 (K1 f2)))))))
      = Bin f0 f1 f2


--------------------------------------------------------------------------------
-- Logic
--------------------------------------------------------------------------------
data Logic_
instance Datatype Logic_ where
    datatypeName _ = "Logic"
    moduleName _ = "Auxiliary.Logic"
data Logic_Var_
data Logic_T_
data Logic_F_
data Logic_Not_
data Logic_Impl_
data Logic_Equiv_
data Logic_Conj_
data Logic_Disj_
instance Constructor Logic_Var_ where
    { conName _ = "Var" }
instance Constructor Logic_T_ where
    { conName _ = "T" }
instance Constructor Logic_F_ where
    { conName _ = "F" }
instance Constructor Logic_Not_ where
    { conName _ = "Not" }
instance Constructor Logic_Impl_ where
    { conName _ = "Impl" }
instance Constructor Logic_Equiv_ where
    { conName _ = "Equiv" }
instance Constructor Logic_Conj_ where
    { conName _ = "Conj" }
instance Constructor Logic_Disj_ where
    { conName _ = "Disj" }

type Rep0Logic_ = D1 Logic_ ((:+:) (C1 Logic_Var_ (S1 NoSelector (Rec0 String)))
  ((:+:) (C1 Logic_T_ (S1 NoSelector U1)) ((:+:) (C1 Logic_F_ 
    (S1 NoSelector U1)) ((:+:) (C1 Logic_Not_ (S1 NoSelector (Rec0 Logic))) 
      ((:+:) (C1 Logic_Impl_ ((:*:) (S1 NoSelector (Rec0 Logic))
        (S1 NoSelector (Rec0 Logic)))) ((:+:) (C1 Logic_Equiv_ ((:*:) 
          (S1 NoSelector (Rec0 Logic)) (S1 NoSelector (Rec0 Logic)))) ((:+:) 
            (C1 Logic_Conj_ ((:*:) (S1 NoSelector (Rec0 Logic)) 
              (S1 NoSelector (Rec0 Logic)))) (C1 Logic_Disj_ ((:*:)
                (S1 NoSelector (Rec0 Logic))
                  (S1 NoSelector (Rec0 Logic)))))))))))

instance Generic Logic where
  type Rep Logic = Rep0Logic_
  {-# INLINE [1] from #-}
  from (Var f0) = M1 (L1 (M1 (M1 (K1 f0))))
  from T = M1 (R1 (L1 (M1 (M1 U1))))
  from F = M1 (R1 (R1 (L1 (M1 (M1 U1)))))
  from (Not f0) = M1 (R1 (R1 (R1 (L1 (M1 (M1 (K1 f0)))))))
  from (Impl f0 f1)
    = M1
        (R1 (R1 (R1 (R1 (L1 (M1 ((:*:) (M1 (K1 f0)) (M1 (K1 f1)))))))))
  from (Equiv f0 f1)
    = M1
        (R1
           (R1 (R1 (R1 (R1 (L1 (M1 ((:*:) (M1 (K1 f0)) (M1 (K1 f1))))))))))
  from (Conj f0 f1)
    = M1
        (R1
           (R1
              (R1 (R1 (R1 (R1 (L1 (M1 ((:*:) (M1 (K1 f0)) (M1 (K1 f1)))))))))))
  from (Disj f0 f1)
    = M1
        (R1
           (R1
              (R1 (R1 (R1 (R1 (R1 (M1 ((:*:) (M1 (K1 f0)) (M1 (K1 f1)))))))))))
  {-# INLINE [1] to #-}
  to (M1 (L1 (M1 (M1 (K1 f0))))) = Var f0
  to (M1 (R1 (L1 (M1 (M1 U1))))) = T
  to (M1 (R1 (R1 (L1 (M1 (M1 U1)))))) = F
  to (M1 (R1 (R1 (R1 (L1 (M1 (M1 (K1 f0)))))))) = Not f0
  to
    (M1 (R1 (R1 (R1 (R1 (L1 (M1 ((:*:) (M1 (K1 f0)) (M1 (K1 f1))))))))))
    = Impl f0 f1
  to
    (M1 (R1 (R1 (R1 (R1 (R1 (L1 (M1 ((:*:) (M1 (K1 f0))
                                         (M1 (K1 f1)))))))))))
    = Equiv f0 f1
  to
    (M1 (R1 (R1 (R1 (R1 (R1 (R1 (L1 (M1 ((:*:) (M1 (K1 f0))
                                             (M1 (K1 f1))))))))))))
    = Conj f0 f1
  to
    (M1 (R1 (R1 (R1 (R1 (R1 (R1 (R1 (M1 ((:*:) (M1 (K1 f0))
                                             (M1 (K1 f1))))))))))))
    = Disj f0 f1

--------------------------------------------------------------------------------
-- Logic
--------------------------------------------------------------------------------
instance Generic Nat where
  type Rep Nat = D1 D1Nat (  C1 C1_0Nat U1
                         :+: C1 C1_1Nat (S1 NoSelector (Rec0 Nat)))

  {-# INLINE [1] from #-}
  from Ze = M1 (L1 (M1 U1))
  from (Su n) = M1 (R1 (M1 (M1 (K1 n))))
  {-# INLINE [1] to #-}
  to (M1 (L1 (M1 U1))) = Ze
  to (M1 (R1 (M1 (M1 (K1 n))))) = Su n

instance Datatype D1Nat where
  datatypeName _ = "Nat"
  moduleName _ = "Code2"

instance Constructor C1_0Nat where
  conName _ = "Ze"

instance Constructor C1_1Nat where
  conName _ = "Su"

data D1Nat
data C1_0Nat
data C1_1Nat
data S1_1_0Nat
