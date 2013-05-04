{-# LANGUAGE RankNTypes, DeriveDataTypeable, MagicHash, CPP #-}
module Main where

{-
-fexpose-all-unfoldings -O2
--show-iface

ModDetails
ModGuts
typeEnvElts md_types
AnId

InlinePragIngo
setInlinePragInfo
setIdUnfolding
-- typeEnvElts md_types
-- IdInfo.unfoldingInfo
-}


-- The main idea:
--  - Eliminate "bad" types (e.g., Data, Typeable, ID)
--     - In higher-order position use memoized specialization
--     - Otherwise inline
--  - Apply the transformations needed to enable the elimination of these "bad" types
--    ??? Could simplifications be driven by where they are needed to enable inline?

-- Problems:
--  - Inlining info missing from everywhere and others
--  - Hard to reference out of scope bindings
--  - Choose inlining order to avoid loops (or extra work)
--  - eqWord and fingerprintFingerprints need to be constant foldable
--    - same for "++"?
--    - And '$WFingerprint???
--  - Need memoizing step
--    - Need general way to avoid recursion?

import Language.Haskell.Syntax

--import Data.Data (foo)

--import Pseudo.Data.Generics (GenericQ, Data, Typeable, mkQ, mkT, extT, gmapT, gmapQ, everywhere, everything)
import Data.Function (fix)
import GHC.Prim -- eqWord#
import GHC.Base((++))

--import Pseudo.Data.Data
--import Pseudo.Data.Typeable
--import Pseudo.Data.Typeable.Internal
--import Pseudo.Data.Typeable.Internal hiding (mkTyCon)
import GHC.Fingerprint (fingerprintFingerprints, Fingerprint(..))
import GHC.Word
import Data.Generics as SYB


{-
everywhere :: (Data b) => (forall a. (Data a) => a -> a) -> (b -> b)
everywhere f = f . gmapT (everywhere f)

everything :: Data a => (r -> r -> r) -> GenericQ r -> a -> r
everything k f x = foldl k (f x) (gmapQ (everything k f) x)
-}

{-

everywhere2 :: (Data b) => (forall a. (Data a) => a -> a) -> (b -> b)
everywhere2 f = worker where
  worker :: (Data b) => b -> b
  worker = f . gmapT worker

data MyPair = MyPair Int Int deriving (Data, Typeable)

mapInt :: (Int -> Int) -> [[Int]] -> [[Int]] --(Int, Int) -> (Int, Int)
mapInt f = everywhere (mkT f)

mapInt2 :: (Int -> Int) -> [Int] -> [Int]
mapInt2 f = worker where
  f' :: (Data a) => a -> a
  f' = mkT f
  worker :: (Data a) => a -> a
  worker = f' . gmapT worker

mapInt3 :: (Int -> Int) -> [Int] -> [Int]
mapInt3 f = worker where
  f' :: (Data a) => a -> a
  f' = mkT f
  worker :: (Data a) => a -> a
  worker = mkT workerInt `extT` workerListInt
  workerInt :: Int -> Int
  workerInt = f' . gmapT worker
  workerListInt :: [Int] -> [Int]
  workerListInt = f' . gmapT worker
-}

-- Cast e (a -> b -> Sym <Axiom>) x y
-- =>
-- Case (e x y) (Sym <Axiom>)

{-# RULES "[]++" forall x. [] ++ x = x #-}
{-# RULES "append" (++) = append #-}

append [] xs = xs
append (y:ys) xs = y : append ys xs

--data INT = INT1 | INT2 deriving (Show, Typeable, Data)
data List a = Nil | Cons a (List a) deriving (Show, Typeable, Data)

mapInt :: (Int -> Int) -> [Int] -> [Int]
mapInt f = everywhere (mkT f)

--mapInt :: (Int -> Int) -> List Int -> List Int --(Int, Int) -> (Int, Int)
--mapInt f = everywhere (mkT f)
  -- NOTE: This is a specialization of "everywhere (mkT f)" on it's first argument

--mapINT :: (INT -> INT) -> List INT -> List INT --(Int, Int) -> (Int, Int)
--mapINT f = everywhere (mkT f)

--everywhereListInt :: (Int -> Int) -> List Int -> List Int
--everywhereListInt f = everywhere (mkT f)

everywhereInt :: (Int -> Int) -> Int -> Int
everywhereInt f = everywhere (mkT f)

listInt :: [Int] -> (Int -> [Int]) -> ([Int] -> [Int] -> [Int]) -> [Int] -> [Int]
listInt z u p = everything p (mkQ z u)

mapIntM :: (Monad m) => (Int -> m Int) -> [Int] -> m [Int]
mapIntM f = everywhereM (mkM f)

map_Int_AST :: (Int -> Int) -> HsModule -> HsModule
map_Int_AST f = everywhere (mkT f)

-- TODO: everything :: [a]
--everythingINT :: ([Int] -> [Int] -> [Int]) -> [Int] -> (Int -> [Int]) -> List Int -> [Int]
--everythingINT add def val = everything add (mkQ def val)

{-
mapInt :: (Int -> Int) -> List Int -> List Int --(Int, Int) -> (Int, Int)
mapInt f = everywhereMapInt where
  -- NOTE: This is a specialization of "everywhere (mkT f)" on it's first argument
  everywhereMapInt :: (Data b) => b -> b
  everywhereMapInt x = mkT f (gmapT everywhereMapInt x)
-}


{-
    let everywhereMapInt_Int :: Int -> Int
        everywhereMapInt_Int = everywhereMapInt
        everywhereMapInt_ListInt :: List Int -> List Int
        everywhereMapInt_ListInt = everywhereMapInt in
      everywhereMapInt_Int `seq` everywhereMapInt
-}
  -- {-# SPECIALIZE everywhereMapInt :: Int -> Int #-}
  -- {-# SPECIALIZE everywhereMapInt :: List Int -> List Int #-}

{-
my_typeOfDefault_go :: [Data.Typeable.Internal.TypeRep] -> [Fingerprint]
my_typeOfDefault_go ts = [f | TypeRep f _ _ <- ts]
-}
{-
map go where
  go (TypeRep f _ _) = f
-}

main = putStrLn (show (mapInt (+1) [])) >> return ()


-- unfold 'everywhere
-- specialize 'everywhere (to $dData, with memoization)
-- unfold '$dData


--What is diff between unfold and inline?
--Need specialize (I don't think fix-spec does what I need)
--Need easy way to add passes (dynamically)
--Need syntax for $fTypeable[]
--Need unfold everywhere, etc.
--Need to get rid of pesky "Cast" forms?  (BTW, what is "Sym"?)
--Do we have a way to manually specify what to rewrite a form to?
--Colors on help (highlight the command names)
--How to constant fold 'eqWord#'?
--Need arrow navigation mode
--Need navigation with context mode (e.g. highlight region), should work well with arrow navigation, press enter to exit
--Need local "{" in the style of matita

--Need 'unfold' with no args
--Need autocomplete for names
--Need 'navigate' for 'back/forward'
--Need named points in tree (name with "{"?)
--Need unfold with multiple arguments
--Need repeat (load "..")
--Report typo (w/ line and collumn) of command name instead of 'type check failed'
--Note that 'add-rule' is in the command table twice

--Need 'force-scrutiny' (or just "repeat force"?)
--  top-ctxt:
--    var -> inline
--    lit -> done
--    app -> recur with app-ctxt
--    lam -> done
--    let -> recur on body
--    case -> recur on scrutiny or simplify-case
--    cast -> recur on body (try elim cast?)
--    tick -> ??
--    type -> error?
--    coercion -> error?
--  app-ctxt:
--    var -> inline
--    lit -> error
--    app -> rec
--    lam -> unfold-lambda
--    let -> let-float-app
--    case -> recur on scrutiny of simplyfy-case
--    cast -> recur on body or apply-cast
--    tick -> ??
--    type -> error?
--    coercion -> error?

--Need 'goto-ref'
--Need 'elim-let" (let-subst)
--Need 'on-let-body'
--'dead-let-elimination' should work on Rec
--Need 'goto-let-body'
--Need 'reload last session'

{-
Cast (Cast x (Sym c)) c -> x
Cast e c -> e if c is trivial (sym, trans, func, tycon, tyconapp, refl, forall, only)

cast-elim
fix-spec
info
remember
save
-}

{-
any-call
  --inline 'everywhere fails
  inline 'mkT --works
$p1Data
$dData
$fData[] --fails
$dTypeable
$fTypeableInt
-}

{-

\ x →
       (case case unsafeDupablePerformIO ▲
        (withArrayLen ▲ ▲ $fStorableFingerprint
                       ((:) ▲
                          (Fingerprint (__word 12354673840372940676) (__word 2337390273253147553))
                          (typeOfDefault_go
                             ((:) ▲
                                ((Cast
                                    ($fTypeableInt) (<Data.Typeable.Internal.NTCo:Typeable <GHC.Types.Int>>))
                                   (undefined ▲))
                                ([] ▲))))
                       (Cast
                          (fingerprintFingerprints1) (<GHC.Types.Int>
-> <GHC.Ptr.Ptr GHC.Fingerprint.Type.Fingerprint>
-> Sym <(GHC.Types.NTCo:IO <GHC.Fingerprint.Type.Fingerprint>)>))) of tpl
               Fingerprint tpl1 tpl2 →
                 TypeRep tpl1 tpl2
                   (TyCon (__word 12354673840372940676) (__word 2337390273253147553)
                      (unpackCString# "main")
                      (unpackCString# "Main")
                      (unpackCString# "List"))
                   ((:) ▲
                      ((Cast
                          ($fTypeableInt) (<Data.Typeable.Internal.NTCo:Typeable <GHC.Types.Int>>))
                         (undefined ▲))
                      ([] ▲)) of wild1
          TypeRep rb2 rb3 ds4 ds5 →
            case eqWord# (__word 16287469036901857884) rb2 of wild2
              False → id ▲
              True →
                case eqWord# (__word 16587023596664995632) rb3 of wild3
                  False → id ▲
                  True →
                    Cast
                      (f) (UnsafeCo GHC.Types.Int (Main.List GHC.Types.Int)
-> UnsafeCo GHC.Types.Int (Main.List GHC.Types.Int)))
         (gmapT ▲ $dData everywhereMapInt x)
-}


-- $fTypeableInt2 = TyCon (__word 16287469036901857884) (__word 16587023596664995632) $fTypeable()_pkg $fTypeable1IO_modl $fTypeableInt3

-- {-# RULES "dummyFingerprint" forall l. fingerprintFingerprints l = Fingerprint undefined undefined #-}

{-
case TypeRep (__word 16287469036901857884) (__word 16587023596664995632) $fTypeableInt2
       ([] ▲) of wild
  TypeRep rb rb1 ds2 ds3 →
    case (let rep =
                case (Cast
                        ($fTypeable1List) (<Data.Typeable.Internal.NTCo:Typeable1 <Main.List>>)) ▲
                       (undefined ▲) of wild
                  TypeRep rb rb1 tc trs →
                    case tc of wild1
                      TyCon rb2 rb3 ds ds1 ds2 →
                        case (++) ▲ trs
                               ((:) ▲
                                  ((Cast
                                      ($fTypeableInt) (<Data.Typeable.Internal.NTCo:Typeable <GHC.Types.Int>>))
                                     (undefined ▲))
                                  ([] ▲)) of wild2
                          [] → TypeRep rb2 rb3 wild1 ([] ▲)
                          (:) ipv ipv1 →
                            case fingerprintFingerprints
                                   ((:) ▲
                                      (Fingerprint rb2 rb3)
                                      (typeOfDefault_go wild2)) of tpl
                              Fingerprint tpl1 tpl2 →
                                TypeRep tpl1 tpl2 wild1 wild2
          in λ ds → rep)
           (gcast3 ▲) of wild1
      TypeRep rb2 rb3 ds4 ds5 →
        case eqWord# rb rb2 of wild2
          False → id ▲
          True →
            case eqWord# rb1 rb3 of wild3
              False → id ▲
              True →
                Cast
                  (f) (UnsafeCo GHC.Types.Int (Main.List GHC.Types.Int)
-> UnsafeCo GHC.Types.Int (Main.List GHC.Types.Int))
(navigation mode; use arrow keys, escape to quit, '?' for help)
(case TypeRep (__word 16287469036901857884) (__word 16587023596664995632) $fTypeableInt2
        ([] ▲) of wild
   TypeRep rb rb1 ds2 ds3 →
     case (let rep =
                 case (Cast
                         ($fTypeable1List) (<Data.Typeable.Internal.NTCo:Typeable1 <Main.List>>)) ▲
                        (undefined ▲) of wild
                   TypeRep rb rb1 tc trs →
                     case tc of wild1
                       TyCon rb2 rb3 ds ds1 ds2 →
                         case (++) ▲ trs
                                ((:) ▲
                                   ((Cast
                                       ($fTypeableInt) (<Data.Typeable.Internal.NTCo:Typeable <GHC.Types.Int>>))
                                      (undefined ▲))
                                   ([] ▲)) of wild2
                           [] → TypeRep rb2 rb3 wild1 ([] ▲)
                           (:) ipv ipv1 →
                             case fingerprintFingerprints
                                    ((:) ▲
                                       (Fingerprint rb2 rb3)
                                       (typeOfDefault_go wild2)) of tpl
                               Fingerprint tpl1 tpl2 →
                                 TypeRep tpl1 tpl2 wild1 wild2
           in λ ds → rep)
            (gcast3 ▲) of wild1
       TypeRep rb2 rb3 ds4 ds5 →
         case eqWord# rb rb2 of wild2
           False → id ▲
           True →
             case eqWord# rb1 rb3 of wild3
               False → id ▲
               True →
                 Cast
                   (f) (UnsafeCo GHC.Types.Int (Main.List GHC.Types.Int)
-> UnsafeCo GHC.Types.Int (Main.List GHC.Types.Int)))
  (gmapT ▲ $dData everywhereMapInt x)
-}




{-
consider 'mapInt
let-intro; nonrec-to-rec; remember; unfold; let-float  -- Install the memoization if bad type in args but not return type
a let bound variable returning a "bad" type should be inlined (via let-subst) (but only in the body? what about recursive values?)
we may want to unfold type variables when determining if a variable returns a "bad" type
we may want to optimize by not giving a new let binding to memoized expressions with no extra arguments

need let-float-bind

another way to think of these rules is that we are eliminating *expressions* with "bad" types
  - with bad type in return, we must inline to expose a constructor so we can match to a case and eliminate it
  - with bad type in argument, we must memoize so those arguments become constants

Maybe memoize only those things that are recursive (or mutually recursive)

Use specialization info on Id instead of stash
-}

--Need "smart" traversal that seeks body of let before branches
--Need to avoid inlining arguments of "everywhere"

{-
foo 'everywhere 3

consider 'mapInt; down; down
let-intro 'everywhere; unshadow; down; remember "everywhere0"; nonrec-to-rec; one-td (unfold 'everywhere); down; down
let-subst-type

if we pull fold info from let binding then ordering isn't so critical

[[Problem: beta-reduce leaves 'let' behind]]
arg/beta-reduce(let-subst)
arg/arg (unfold)
arg/case/cast (inline)
sym-cast
arg/case (case-reduce)


case-reduce always on bad-types


bad type in case
bad type as let binding
bad type as argument to function


always consider highest point at which bad types appear:
  fun **arg** (then (force x until?) beta-reduce fun)
  case **x** (then force x until case-reduce)
  case Cast **x** (then inline x)
  case Cast Cast .. (then sym-cast-elim)

always: refl-cast-elim
        let-elim-unused
let float

force:
  var inline
  let let-float


dead-let-elimination
force



let-subst



let-float-cast???



eval-fingerprintFingerprints
eqWord-elim
we may need to consider fingerprints to also be bad
'let' prevents memoization from recognizing itself (perhaps make memoization look through arguments?)

Does sym-cast-elim need to look through let bindings?


-- Has no bad types but should be simplified:
case False of wild2
     False → id ▲
     True →
       case False of wild3
         False → id ▲
         True →
           Cast
             (eta) (UnsafeCo GHC.Types.Int (Main.List GHC.Types.Int)
-> UnsafeCo GHC.Types.Int (Main.List GHC.Types.Int))


-}


{-
mapINT = λ f →
  let rec memo_everywhere =
            (.) ▲ ▲ ▲
              (let rec memo_f =
                         (let rec memo_mkT = λ eta →
                                    case False of wild2
                                      False → id ▲
                                      True →
                                        case False of wild3
                                          False → id ▲
                                          True → eta
                          in memo_mkT) f
               in memo_f)
              (let rec memo_gmapT =
                         let rec memo_$cgmapT = λ x0 →
                                   let rec memo_unID =
                                             Cast
                                               (let z =
                                                      Cast
                                                        (λ ▹ tpl →
                                                           tpl) (forall x. <x> -> Sym <(Data.Data.NTCo:ID <x>)>)
                                                in case x0 of wild
                                                     Nil → z ▲ (Nil ▲)
                                                     Cons a1 a2 →
                                                       (let rec memo_k =
                                                                  Cast
                                                                    (λ x →
                                                                       (λ x →
                                                                          (λ tpl →
                                                                             tpl)
                                                                            (Cons ▲)
                                                                            ((let rec memo_f =
                                                                                        let rec memo_everywhere =
                                                                                                  (.) ▲ ▲ ▲
                                                                                                    (let rec memo_f =
                                                                                                               (let rec memo_mkT = λ eta →
                                                                                                                          case True of wild2
                                                                                                                            False →
                                                                                                                              id ▲
                                                                                                                            True →
                                                                                                                              case True of wild3
                                                                                                                                False →
                                                                                                                                  id ▲
                                                                                                                                True →
                                                                                                                                  eta
                                                                                                                in memo_mkT) f
                                                                                                     in memo_f)
                                                                                                    (let rec memo_gmapT =
                                                                                                               let rec memo_$cgmapT =
                                                                                                                         let rec memo_$dmgmapT = λ x0 →
                                                                                                                                   let rec memo_unID =
                                                                                                                                             Cast
                                                                                                                                               (let z =
                                                                                                                                                      Cast
                                                                                                                                                        (λ ▹ tpl →
                                                                                                                                                           tpl) (forall x. <x> -> Sym <(Data.Data.NTCo:ID <x>)>)
                                                                                                                                                in case x0 of wild
                                                                                                                                                     INT1 →
                                                                                                                                                       z ▲ INT1
                                                                                                                                                     INT2 →
                                                                                                                                                       z ▲ INT2) (<Data.Data.NTCo:ID <Main.INT>>)
                                                                                                                                   in memo_unID
                                                                                                                         in memo_$dmgmapT
                                                                                                               in memo_$cgmapT
                                                                                                     in memo_gmapT)
                                                                                        in memo_everywhere
                                                                              in memo_f) x)) a1
                                                                         ((let rec memo_f =
                                                                                     let rec memo_everywhere =
                                                                                               (.) ▲ ▲ ▲
                                                                                                 (let rec memo_f =
                                                                                                            (let rec memo_mkT = λ eta →
                                                                                                                       case False of wild2
                                                                                                                         False →
                                                                                                                           id ▲
                                                                                                                         True →
                                                                                                                           case False of wild3
                                                                                                                             False →
                                                                                                                               id ▲
                                                                                                                             True →
                                                                                                                               eta
                                                                                                             in memo_mkT) f
                                                                                                  in memo_f)
                                                                                                 memo_$cgmapT
                                                                                     in memo_everywhere
                                                                           in memo_f) x)) (<Main.List Main.INT>
-> Sym <(Data.Data.NTCo:ID <Main.List Main.INT>)>)
                                                        in memo_k) a2) (<Data.Data.NTCo:ID <Main.List Main.INT>>)
                                   in memo_unID
                         in memo_$cgmapT
               in memo_gmapT)
  in memo_everywhere
hermit<588> simplify
mapINT = λ f →
  let g =
        let rec memo_$cgmapT = λ x0 →
                  Cast
                    (case x0 of wild
                       Nil →
                         (Cast
                            (λ ▹ tpl →
                               tpl) (forall x. <x> -> Sym <(Data.Data.NTCo:ID <x>)>)) ▲
                           (Nil ▲)
                       Cons a1 a2 →
                         (Cast
                            (λ x →
                               Cons ▲
                                 (f (Cast
                                       (let z =
                                              Cast
                                                (λ ▹ tpl →
                                                   tpl) (forall x. <x> -> Sym <(Data.Data.NTCo:ID <x>)>)
                                        in case a1 of wild
                                             INT1 → z ▲ INT1
                                             INT2 →
                                               z ▲ INT2) (<Data.Data.NTCo:ID <Main.INT>>)))
                                 (id ▲
                                    (memo_$cgmapT x))) (<Main.List Main.INT>
-> Sym <(Data.Data.NTCo:ID <Main.List Main.INT>)>)) a2) (<Data.Data.NTCo:ID <Main.List Main.INT>>)
        in memo_$cgmapT
  in λ x → id ▲ (g x)
-}


{- Default GHC passes:
[CoreDoNothing, CoreDoNothing, Simplifier, Specialise,
 Float out(FOS {Lam = Just 0, Consts = True, PAPs = False}),
 Float inwards, CoreDoPasses, CoreDoPasses, CoreDoPasses,
 Float out(FOS {Lam = Just 0, Consts = True, PAPs = True}),
 Common sub-expression, Float inwards, CoreDoNothing, CoreDoPasses,
 SpecConstr, CoreDoNothing, CoreDoPasses]
-}

foo :: (Int -> Int) -> [Int] -> [Int]
foo f = SYB.everywhere (SYB.mkT f)


{-

~470 iterations, then simplify
~4GB ram(!)

λ f →
  let g =
        let rec memo_tpl = λ ds1 →
                  case ds1 of wild
                    [] → [] ▲
                    (:) x xs → (:) ▲ (f x) (id ▲ (memo_tpl xs))
        in memo_tpl
  in λ x → id ▲ (g x)

-}


foo1 :: (Data a) => (a -> a) -> [Char] -> [Char]
foo1 f = mkT f


foo2 :: (Data a) => (a -> a) -> SrcLoc -> SrcLoc
foo2 f = mkT f

-- Better solution is to avoid map and mark the recursive function as inlinable
{-# RULES "map" forall f xs. map f xs = myMap f xs #-}

myMap _ []     = []
myMap f (x:xs) = f x : myMap f xs
