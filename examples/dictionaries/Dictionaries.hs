{-# LANGUAGE RankNTypes, InstanceSigs, ScopedTypeVariables #-}

module Main where

import Prelude hiding (abs)

import Data.Function (fix)

import Unsafe.Coerce

data TypeRep = T_Int | T_List TypeRep | T_Fun TypeRep TypeRep -- deriving Eq

eqTyRep :: TypeRep -> TypeRep -> Bool
eqTyRep T_Int          T_Int = True
eqTyRep (T_List t1)    (T_List t2) = eqTyRep t1 t2
eqTyRep (T_Fun t1 t1') (T_Fun t2 t2') = eqTyRep t1 t2 && eqTyRep t1' t2'
eqTyRep _              _              = False

class Data a where
  gmapT :: (forall b. (Data b) => b -> b) -> a -> a
  typeOf :: a -> TypeRep

instance Data Int where
  gmapT _ x = x
  typeOf _ = T_Int

instance Data a => Data [a] where
  gmapT h [] = []
  gmapT h (x : xs) = h x : h xs
  typeOf x = T_List (typeOf (head x))

inc :: (forall b. (Data b) => b -> b)
inc = undefined

everywhere  :: (Data a) => a -> a
everywhere x = inc (gmapT everywhere x)

-- everywhere' :: forall a. Data a => a -> a
-- everywhere' = undefined
--    where fix' :: ((forall x. Data x => x -> x) -> (forall y. Data y => y -> y)) -> (forall z. Data z => z -> z)
--          fix' = fix

-- everywhereListInt :: [Int] -> [Int]
-- everywhereListInt = everywhere

------

-- everywhere2Int :: Int -> Int
-- everywhere2Int = mkT inc

-- everywhere2ListInt :: [Int] -> [Int]
-- everywhere2ListInt [] = []
-- everywhere2ListInt (x : xs) = mkT inc (everywhere2Int x : everywhere2ListInt xs)

-----

gmapTInt :: Int -> Int
gmapTInt = id

gmapTListInt :: [Int] -> [Int]
gmapTListInt [] = []
gmapTListInt (x : xs) = everywhereInt x : everywhereListInt xs

everywhereInt :: Int -> Int
everywhereInt x = inc (gmapTInt x)

everywhereListInt :: [Int] -> [Int]
everywhereListInt x = inc (gmapTListInt x)

-----


type T1 = forall a. (Data a) => a -> a
type T2 = (Int -> Int, [Int] -> [Int])

rep :: T1 -> T2
rep t1 = (t1 :: Int -> Int, t1 :: [Int] -> [Int])

-- abs (f1, f2) = mkT f1 `extT` f2
abs :: T2 -> T1
abs (f1, f2) x = if T_Int `eqTyRep` typeOf x
                  then unsafeCoerce (f1 (unsafeCoerce x))
                  else if T_List T_Int `eqTyRep` typeOf x
                        then unsafeCoerce (f2 (unsafeCoerce x))
                        else x


f :: T1 -> T1
f f' x = inc (gmapT f' x)

{-
  fix (abs . rep . f) = fix f
<=>
  abs (rep ( t1) x == t1 x
<=>
  abs (t1 :: Int -> Int, t1 :: [Int] -> [Int]) x == t1 x
<=>
-}

absrep :: T1 -> T1
absrep t1 x = abs (rep t1) x

absrepf :: T1 -> T1
absrepf t1 x = abs (rep (f t1)) x

repfabs :: T2 -> T2
repfabs t2 = rep (f (abs t2))

main :: IO ()
main = print "hello"