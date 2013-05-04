{-# LANGUAGE EmptyDataDecls        #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE GADTs                 #-}

module Auxiliary.InstantInline where

import Auxiliary.Nat (Nat(..))
import Auxiliary.Tree (Tree(..))
import Auxiliary.Logic (Logic(..))
import Auxiliary.InstantBase hiding (Var(..))
import qualified Auxiliary.InstantBase as G (Var(..))


-- ig Nat instances

data Ze
instance Constructor Ze  where conName _ = "Ze"
data Su
instance Constructor Su where conName _ = "Su"


instance Representable Nat where
  type Rep Nat = C Ze U :+: C Su (Rec Nat)
  
  {-# INLINE [1] from #-}
  from (Su n) = R (C (Rec n))
  from Ze     = L (C U)

  {-# INLINE [1] to #-}
  to (R (C (Rec n))) = Su n
  to (L (C U)) = Ze
  
-- ig Tree instances

data Bin
instance Constructor Bin  where conName _ = "Bin"
data Leaf
instance Constructor Leaf where conName _ = "Leaf"


instance Representable (Tree a) where
  type Rep (Tree a) =     C Leaf U
                      :+: C Bin  (G.Var a :*: Rec (Tree a) :*: Rec (Tree a))

  {-# INLINE [1] from #-}
  from (Bin x l r) = R (C (G.Var x :*: Rec l :*: Rec r))
  from Leaf        = L (C U)

  {-# INLINE [1] to #-}
  to (R (C (G.Var x :*: (Rec l) :*: (Rec r)))) = Bin x l r
  to (L (C U))                                 = Leaf


-- ig Logic instances

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
    
type RepLogic =
      (C Logic_Var_ (G.Var String))
  :+: (C Logic_T_ U)
  :+: (C Logic_F_ U)
  :+: (C Logic_Not_ (Rec Logic))
  :+: (C Logic_Impl_ (Rec Logic :*: Rec Logic))
  :+: (C Logic_Equiv_ (Rec Logic :*: Rec Logic))
  :+: (C Logic_Conj_ (Rec Logic :*: Rec Logic))
  :+: (C Logic_Disj_ (Rec Logic :*: Rec Logic))


instance Representable Logic where
  type Rep Logic = RepLogic

  {-# INLINE [1] from #-}
  from (Var f0) = L (C (G.Var f0))
  from T = R (L (C U))
  from F = R (R (L (C U)))
  from (Not f0) = R (R (R (L (C (Rec f0)))))
  from (Impl f0 f1) = R (R (R (R (L (C ((:*:) (Rec f0) (Rec f1)))))))
  from (Equiv f0 f1) = R (R (R (R (R (L (C ((:*:) (Rec f0) (Rec f1))))))))
  from (Conj f0 f1) = R (R (R (R (R (R (L (C ((:*:) (Rec f0) (Rec f1)))))))))
  from (Disj f0 f1) = R (R (R (R (R (R (R (C ((:*:) (Rec f0) (Rec f1)))))))))

  {-# INLINE [1] to #-}
  to (L (C (G.Var f0))) = Var f0
  to (R (L (C U))) = T
  to (R (R (L (C U)))) = F
  to (R (R (R (L (C (Rec f0)))))) = Not f0
  to (R (R (R (R (L (C ((:*:) (Rec f0) (Rec f1)))))))) = Impl f0 f1
  to (R (R (R (R (R (L (C ((:*:) (Rec f0) (Rec f1))))))))) = Equiv f0 f1
  to (R (R (R (R (R (R (L (C ((:*:) (Rec f0) (Rec f1)))))))))) = Conj f0 f1
  to (R (R (R (R (R (R (R (C ((:*:) (Rec f0) (Rec f1)))))))))) = Disj f0 f1
