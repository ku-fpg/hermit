{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Auxiliary.EMGM where

import Auxiliary.Tree (Tree(..))
import Auxiliary.Logic (Logic(..))
import Generics.EMGM.Common
import Generics.EMGM.Data.List
import Generics.EMGM.Functions.Everywhere


-- EMGM instances for Tree
epTree = EP from' to' where
  from' Leaf        = L Unit
  from' (Bin x l r) = R (x :*: l :*: r)
  to' (L Unit)            = Leaf
  to' (R (x :*: l :*: r)) = (Bin x l r)

conLeaf, conBin :: ConDescr
conLeaf = ConDescr {
  conName = "Leaf",
  conArity = 0, conLabels = [], conFixity = Nonfix
  }
conBin = ConDescr {
  conName = "Bin",
  conArity = 3, conLabels = [], conFixity = Nonfix
  }

rTree :: Generic g => g a -> g (Tree a)
rTree ra = rtype epTree 
            (rsum 
              (rcon conLeaf runit)
              (rcon conBin (rprod ra (rprod (rTree ra) (rTree ra)))))

instance (Generic g, Rep g a) => Rep g (Tree a) where
  rep = rTree rep

instance Generic g => FRep g Tree where
  frep = rTree

rTree2 :: Generic2 g => g a b -> g (Tree a) (Tree b)
rTree2 ra = rtype2 epTree epTree 
              (rsum2 
                (rcon2 conLeaf runit2)
                (rcon2 conBin (rprod2 ra (rprod2 (rTree2 ra) (rTree2 ra)))))

instance Generic2 g => FRep2 g Tree where
  frep2 = rTree2

-- EMGM instances for Logic
--
-- The code below is resulting from TH generation. We paste it instead of
-- just invoking TH because the TH in 6.12 and 6.13 is not compatible with
-- the libraries yet.

conVar :: ConDescr
conVar = ConDescr
           "Var" 1 [] Nonfix
conImpl :: ConDescr
conImpl = ConDescr
            "Impl" 2 [] Nonfix
conEquiv :: ConDescr
conEquiv = ConDescr
             "Equiv" 2 [] Nonfix
conConj :: ConDescr
conConj = ConDescr
            "Conj" 2 [] Nonfix
conDisj :: ConDescr
conDisj = ConDescr
            "Disj" 2 [] Nonfix
conNot :: ConDescr
conNot = ConDescr
           "Not" 1 [] Nonfix
conT :: ConDescr
conT = ConDescr
         "T" 0 [] Nonfix
conF :: ConDescr
conF = ConDescr
         "F" 0 [] Nonfix
epLogic :: EP Logic (String :+: (((:*:) Logic Logic) :+: ((:+:) ((:*:) Logic Logic) ((:+:) ((:*:) Logic Logic) ((:+:) ((:*:) Logic Logic) ((:+:) Logic ((:+:) Unit Unit)))))))
epLogic = EP from to
        where
            from (Var v1)
                         = L v1
            from (Impl v1 v2)
                         = R
                             (L
                                (v1 :*: v2))
            from (Equiv v1 v2)
                         = R
                             (R
                                (L
                                   (v1 :*: v2)))
            from (Conj v1 v2)
                         = R
                             (R
                                (R
                                   (L
                                      (v1 :*: v2))))
            from (Disj v1 v2)
                         = R
                             (R
                                (R
                                   (R
                                      (L
                                         (v1
                                        :*:
                                          v2)))))
            from (Not v1)
                         = R
                             (R
                                (R
                                   (R
                                      (R
                                         (L v1)))))
            from T
                         = R
                             (R
                                (R
                                   (R
                                      (R
                                         (R
                                            (L
                                               Unit))))))
            from F
                         = R
                             (R
                                (R
                                   (R
                                      (R
                                         (R
                                            (R
                                               Unit))))))
            to (L v1)
                       = Var v1
            to (R (L (v1 :*: v2)))
                       = Impl v1 v2
            to (R (R (L (v1 :*: v2))))
                       = Equiv v1 v2
            to (R (R (R (L (v1 :*: v2)))))
                       = Conj v1 v2
            to (R (R (R (R (L (v1 :*: v2))))))
                       = Disj v1 v2
            to (R (R (R (R (R (L v1))))))
                       = Not v1
            to (R (R (R (R (R (R (L Unit)))))))
                       = T
            to (R (R (R (R (R (R (R Unit)))))))
                       = F
repLogic :: (Generic g, Rep g String, Rep g Logic) => g Logic
repLogic = rtype
             epLogic
             (rsum
                (rcon
                   conVar rep)
                (rsum
                   (rcon
                      conImpl
                      (rprod
                         rep rep))
                   (rsum
                      (rcon
                         conEquiv
                         (rprod
                            rep rep))
                      (rsum
                         (rcon
                            conConj
                            (rprod
                               rep rep))
                         (rsum
                            (rcon
                               conDisj
                               (rprod
                                  rep
                                  rep))
                            (rsum
                               (rcon
                                  conNot rep)
                               (rsum
                                  (rcon
                                     conT runit)
                                  (rcon
                                     conF runit))))))))
frepLogic :: (Generic g) => g Logic
frepLogic = rtype
              epLogic
              (rsum
                 (rcon
                    conVar (frepList rchar))
                 (rsum
                    (rcon
                       conImpl (rprod frepLogic frepLogic))
                    (rsum
                       (rcon
                          conEquiv (rprod frepLogic frepLogic))
                       (rsum
                          (rcon
                             conConj (rprod frepLogic frepLogic))
                          (rsum
                             (rcon
                                conDisj
                                (rprod frepLogic frepLogic))
                             (rsum
                                (rcon conNot frepLogic)
                                (rsum
                                   (rcon
                                      conT runit)
                                   (rcon
                                      conF runit))))))))
frep2Logic :: (Generic2 g) => g Logic Logic
frep2Logic = rtype2
               epLogic
               epLogic
               (rsum2
                  (rcon2
                     conVar (frep2List rchar2))
                  (rsum2
                     (rcon2
                        conImpl (rprod2 frep2Logic frep2Logic))
                     (rsum2
                        (rcon2
                           conEquiv
                           (rprod2 frep2Logic frep2Logic))
                        (rsum2
                           (rcon2
                              conConj
                              (rprod2 frep2Logic frep2Logic))
                           (rsum2
                              (rcon2
                                 conDisj
                                 (rprod2 frep2Logic frep2Logic))
                              (rsum2
                                 (rcon2 conNot frep2Logic)
                                 (rsum2
                                    (rcon2
                                       conT runit2)
                                    (rcon2
                                       conF runit2))))))))
frep3Logic :: (Generic3 g) => g Logic Logic Logic
frep3Logic = rtype3
               epLogic
               epLogic
               epLogic
               (rsum3
                  (rcon3
                     conVar (frep3List rchar3))
                  (rsum3
                     (rcon3
                        conImpl (rprod3 frep3Logic frep3Logic))
                     (rsum3
                        (rcon3
                           conEquiv
                           (rprod3 frep3Logic frep3Logic))
                        (rsum3
                           (rcon3
                              conConj
                              (rprod3 frep3Logic frep3Logic))
                           (rsum3
                              (rcon3
                                 conDisj
                                 (rprod3 frep3Logic frep3Logic))
                              (rsum3
                                 (rcon3 conNot frep3Logic)
                                 (rsum3
                                    (rcon3
                                       conT runit3)
                                    (rcon3
                                       conF runit3))))))))
bifrep2Logic :: (Generic2 g) => g Logic Logic
bifrep2Logic = rtype2
                 epLogic
                 epLogic
                 (rsum2
                    (rcon2
                       conVar (bifrep2List rchar2))
                    (rsum2
                       (rcon2
                          conImpl
                          (rprod2 bifrep2Logic bifrep2Logic))
                       (rsum2
                          (rcon2
                             conEquiv
                             (rprod2 bifrep2Logic bifrep2Logic))
                          (rsum2
                             (rcon2
                                conConj
                                (rprod2
                                   bifrep2Logic bifrep2Logic))
                             (rsum2
                                (rcon2
                                   conDisj
                                   (rprod2
                                      bifrep2Logic bifrep2Logic))
                                (rsum2
                                   (rcon2 conNot bifrep2Logic)
                                   (rsum2
                                      (rcon2
                                         conT runit2)
                                      (rcon2
                                         conF runit2))))))))

instance (Generic g,
          Rep g String,
          Rep g Logic) =>
         Rep g Logic where
    { rep = repLogic }
{-
instance Rep (Generics.EMGM.Functions.Collect.Collect Logic) Logic where
    { rep = Generics.EMGM.Functions.Collect.Collect
                                        (\ x[a32G] -> [x[a32G]]) }
-}
instance (Rep (Everywhere Logic) String,
          Rep (Everywhere Logic) Logic) =>
         Rep (Everywhere Logic) Logic where
      rep = Everywhere
                                        (\ f x
                                             -> case x of
                                                  (Var v1)
                                                    -> f (Var
                                                            (selEverywhere
                                                               rep
                                                               f
                                                               v1))
                                                  (Impl v1 v2)
                                                    -> f (Impl
                                                            (selEverywhere
                                                               rep
                                                               f
                                                               v1)
                                                            (selEverywhere
                                                               rep
                                                               f
                                                               v2))
                                                  (Equiv v1 v2)
                                                    -> f (Equiv
                                                            (selEverywhere
                                                               rep
                                                               f
                                                               v1)
                                                            (selEverywhere
                                                               rep
                                                               f
                                                               v2))
                                                  (Conj v1 v2)
                                                    -> f (Conj
                                                            (selEverywhere
                                                               rep
                                                               f
                                                               v1)
                                                            (selEverywhere
                                                               rep
                                                               f
                                                               v2))
                                                  (Disj v1 v2)
                                                    -> f (Disj
                                                            (selEverywhere
                                                               rep
                                                               f
                                                               v1)
                                                            (selEverywhere
                                                               rep
                                                               f
                                                               v2))
                                                  (Not v1)
                                                    -> f (Not
                                                            (selEverywhere
                                                               rep
                                                               f
                                                               v1))
                                                  T -> f T
                                                  F
                                                    -> f F)
instance Rep (Everywhere' Logic) Logic where
    { rep = Everywhere'
                                        (\ f x -> f x) }
