{-# LANGUAGE EmptyDataDecls        #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}

module Auxiliary.RegularInline where

import Auxiliary.Tree (Tree(..))
import Auxiliary.Logic (Logic(..))
import Generics.Regular


-- Regular Tree instances
data Bin
instance Constructor Bin  where conName _ = "Bin"
data Leaf
instance Constructor Leaf where conName _ = "Leaf"

type instance PF (Tree a) =       C Bin  (K a :*: I :*: I)
                              :+: C Leaf U

instance Regular (Tree a) where
  from = fromTree
  to   = toTree

{-# INLINE [1] fromTree #-}
fromTree (Bin x l r) = L (C (K x :*: I l :*: I r))
fromTree Leaf        = R (C U)

{-# INLINE [1] toTree #-}
toTree (L (C (K x :*: (I l) :*: (I r)))) = Bin x l r
toTree (R (C U))                         = Leaf

-- Regular Logic instances
{-
-- Balanced view
type instance PF Logic =
        (((C Var (K String)) :+: C Equiv (I :*: I))
      :+:
        (C Impl (I :*: I) :+: C Conj (I :*: I)))
    :+:
        ((C Disj (I :*: I) :+: C Not I)
      :+: 
        (C T U :+: C F U))

instance Regular Logic where
  from (Var x)     = L (L (L (C (K x))))
  from (Equiv p q) = L (L (R (C ((I p) :*: (I q)))))
  from (Impl p q)  = L (R (L (C ((I p) :*: (I q)))))
  from (Conj p q)  = L (R (R (C ((I p) :*: (I q)))))
  from (Disj p q)  = R (L (L (C ((I p) :*: (I q)))))
  from (Not p)     = R (L (R (C (I p))))
  from T           = R (R (L (C U)))
  from F           = R (R (R (C U)))

  to (L (L (L (C (K x)))))             = Var x
  to (L (L (R (C ((I p) :*: (I q)))))) = Equiv p q
  to (L (R (L (C ((I p) :*: (I q)))))) = Impl p q
  to (L (R (R (C ((I p) :*: (I q)))))) = Conj p q
  to (R (L (L (C ((I p) :*: (I q)))))) = Disj p q
  to (R (L (R (C (I p)))))             = Not p
  to (R (R (L (C U))))                 = T
  to (R (R (R (C U))))                 = F
-}


-- The code below is resulting from TH generation. We paste it instead of
-- just invoking TH because the TH in 6.12 and 6.13 is not compatible with
-- the libraries yet.

data Logic_Var_
data Logic_Impl_
data Logic_Equiv_
data Logic_Conj_
data Logic_Disj_
data Logic_Not_
data Logic_T_
data Logic_F_

instance Constructor Logic_Var_ where
    { conName _ = "Var" }
instance Constructor Logic_Impl_ where
    { conName _ = "Impl" }
instance Constructor Logic_Equiv_ where
    { conName _ = "Equiv" }
instance Constructor Logic_Conj_ where
    { conName _ = "Conj" }
instance Constructor Logic_Disj_ where
    { conName _ = "Disj" }
instance Constructor Logic_Not_ where
    { conName _ = "Not" }
instance Constructor Logic_T_ where
    { conName _ = "T" }
instance Constructor Logic_F_ where
    { conName _ = "F" }
    
type PFLogic =
      (C Logic_Var_ (K String))
  :+: (C Logic_T_ U)
  :+: (C Logic_F_ U)
  :+: (C Logic_Not_ I)
  :+: (C Logic_Impl_ ((:*:) I I))
  :+: (C Logic_Equiv_ ((:*:) I I))
  :+: (C Logic_Conj_ ((:*:) I I))
  :+: (C Logic_Disj_ ((:*:) I I))

type instance PF Logic = PFLogic
instance Regular Logic where
  from = fromLogic  
  to   = toLogic

{-# INLINE [1] fromLogic #-}
fromLogic (Var f0) = L (C (K f0))
fromLogic T = R (L (C U))
fromLogic F = R (R (L (C U)))
fromLogic (Not f0) = R (R (R (L (C (I f0)))))
fromLogic (Impl f0 f1) = R (R (R (R (L (C ((:*:) (I f0) (I f1)))))))
fromLogic (Equiv f0 f1) = R (R (R (R (R (L (C ((:*:) (I f0) (I f1))))))))
fromLogic (Conj f0 f1) = R (R (R (R (R (R (L (C ((:*:) (I f0) (I f1)))))))))
fromLogic (Disj f0 f1) = R (R (R (R (R (R (R (C ((:*:) (I f0) (I f1)))))))))

{-# INLINE [1] toLogic #-}
toLogic (L (C (K f0))) = Var f0
toLogic (R (L (C U))) = T
toLogic (R (R (L (C U)))) = F
toLogic (R (R (R (L (C (I f0)))))) = Not f0
toLogic (R (R (R (R (L (C ((:*:) (I f0) (I f1)))))))) = Impl f0 f1
toLogic (R (R (R (R (R (L (C ((:*:) (I f0) (I f1))))))))) = Equiv f0 f1
toLogic (R (R (R (R (R (R (L (C ((:*:) (I f0) (I f1)))))))))) = Conj f0 f1
toLogic (R (R (R (R (R (R (R (C ((:*:) (I f0) (I f1)))))))))) = Disj f0 f1
