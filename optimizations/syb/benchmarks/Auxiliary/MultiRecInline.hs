{-# LANGUAGE EmptyDataDecls        #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TemplateHaskell       #-}

module Auxiliary.MultiRecInline where

import Auxiliary.Tree (Tree(..))
import Auxiliary.Logic (Logic(..))
import Auxiliary.MultirecInlineBase


-- MultiRecInline Tree instances
data TreeF :: * -> * where
  Tree :: TreeF (Tree Int)
  
type instance PF TreeF =
      ((C Bin  (K Int :*: I (Tree Int) :*: I (Tree Int))) -- |Bin|
  :+: (C Leaf U))                                         -- |Leaf|
    :>: (Tree Int)

instance Fam TreeF where
  {-# INLINE [1] from #-}
  from Tree (Bin x l r) = Tag (L (C (K x :*: I (I0 l) :*: I (I0 r))))
  from Tree Leaf        = Tag (R (C U))

  {-# INLINE [1] to #-}
  to Tree (Tag (L (C (K x :*: (I (I0 l)) :*: (I (I0 r)))))) = Bin x l r
  to Tree (Tag (R (C U)))                                   = Leaf
  
instance El TreeF (Tree Int) where
  proof = Tree

data Bin
instance Constructor Bin  where conName _ = "Bin"
data Leaf
instance Constructor Leaf where conName _ = "Leaf"

instance EqS TreeF where
  {-# INLINE [1] eqS #-}
  eqS Tree Tree = Just Refl

-- MultiRecInline Logic instances

-- The code below is resulting from TH generation. We paste it instead of
-- just invoking TH because the TH in 6.12 and 6.13 is not compatible with
-- the libraries yet.

data LogicF :: * -> * where
  Logic :: LogicF Logic

data Var
data Impl
data Equiv
data Conj
data Disj
data Not
data T
data F

instance Constructor Var where
    { conName _ = "Var" }
instance Constructor Impl where
    { conName _ = "Impl" }
instance Constructor Equiv where
    { conName _ = "Equiv" }
instance Constructor Conj where
    { conName _ = "Conj" }
instance Constructor Disj where
    { conName _ = "Disj" }
instance Constructor Not where
    { conName _ = "Not" }
instance Constructor T where
    { conName _ = "T" }
instance Constructor F where
    { conName _ = "F" }

type PFLogic =
    (:>:) ((:+:) (C Var (K String)) ((:+:) (C Impl ((:*:) (I Logic) (I Logic))) ((:+:) (C Equiv ((:*:) (I Logic) (I Logic))) ((:+:) (C Conj ((:*:) (I Logic) (I Logic))) ((:+:) (C Disj ((:*:) (I Logic) (I Logic))) ((:+:) (C Not (I Logic)) ((:+:) (C T U) (C F U)))))))) Logic

type instance PF LogicF = PFLogic

instance El LogicF Logic where
      proof = Logic
instance Fam LogicF where
      {-# INLINE [1] from #-}
      from Logic (Var f0)
                                    = Tag
                                        (L
                                           (C
                                              (K f0)))
      from Logic (Impl f0 f1)
                                    = Tag
                                        (R
                                           (L
                                              (C
                                                 ((:*:)
                                                    (I
                                                       (I0 f0))
                                                    (I
                                                       (I0 f1))))))
      from Logic (Equiv f0 f1)
                                    = Tag
                                        (R
                                           (R
                                              (L
                                                 (C
                                                    ((:*:)
                                                       (I
                                                          (I0 f0))
                                                       (I
                                                          (I0
                                                             f1)))))))
      from Logic (Conj f0 f1)
                                    = Tag
                                        (R
                                           (R
                                              (R
                                                 (L
                                                    (C
                                                       ((:*:)
                                                          (I
                                                             (I0 f0))
                                                          (I
                                                             (I0
                                                                f1))))))))
      from Logic (Disj f0 f1)
                                    = Tag
                                        (R
                                           (R
                                              (R
                                                 (R
                                                    (L
                                                       (C
                                                          ((:*:)
                                                             (I
                                                                (I0
                                                                   f0))
                                                             (I
                                                                (I0
                                                                   f1)))))))))
      from Logic (Not f0)
                                    = Tag
                                        (R
                                           (R
                                              (R
                                                 (R
                                                    (R
                                                       (L
                                                          (C
                                                             (I
                                                                (I0
                                                                   f0)))))))))
      from Logic T
                                    = Tag
                                        (R
                                           (R
                                              (R
                                                 (R
                                                    (R
                                                       (R
                                                          (L
                                                             (C
                                                                U))))))))
      from Logic F
                                    = Tag
                                        (R
                                           (R
                                              (R
                                                 (R
                                                    (R
                                                       (R
                                                          (R
                                                             (C
                                                                U))))))))
      {-# INLINE [1] to #-}
      to Logic
                                (Tag (L (C (K f0))))
                                  = Var f0
      to Logic
                                (Tag (R (L (C ((:*:) (I (I0 f0))
                                                                                                                                                                 (I (I0 f1)))))))
                                  = Impl f0 f1
      to Logic
                                (Tag (R (R (L (C ((:*:) (I (I0 f0))
                                                                                                                                                                                          (I (I0 f1))))))))
                                  = Equiv f0 f1
      to Logic
                                (Tag (R (R (R (L (C ((:*:) (I (I0 f0))
                                                                                                                                                                                                                   (I (I0 f1)))))))))
                                  = Conj f0 f1
      to Logic
                                (Tag (R (R (R (R (L (C ((:*:) (I (I0 f0))
                                                                                                                                                                                                                                            (I (I0 f1))))))))))
                                  = Disj f0 f1
      to Logic
                                (Tag (R (R (R (R (R (L (C (I (I0 f0))))))))))
                                  = Not f0
      to Logic
                                (Tag (R (R (R (R (R (R (L (C U)))))))))
                                  = T
      to Logic
                                (Tag (R (R (R (R (R (R (R (C U)))))))))
                                  = F
instance EqS LogicF where
  {-# INLINE [1] eqS #-}
  eqS Logic Logic = Just Refl
