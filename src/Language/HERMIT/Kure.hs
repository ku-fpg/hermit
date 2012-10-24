{-# LANGUAGE MultiParamTypeClasses, TypeFamilies, FlexibleInstances, FlexibleContexts, TupleSections, LambdaCase, InstanceSigs #-}

-- Note: InstanceSigs don't expand type families (annoyingly), as of GHC 7.6.1.  Check if this has been fixed in the next version.

module Language.HERMIT.Kure
       (
       -- * KURE Modules

       -- | All the required functionality of KURE is exported here, so other modules do not need to import KURE directly.
         module Language.KURE
       , module Language.KURE.Injection
       , KureM, runKureM, fromKureM
       -- * Synonyms
       -- | In HERMIT, 'Translate', 'Rewrite' and 'Lens' always operate on the same context and monad.
       , TranslateH
       , RewriteH
       , LensH
       , idR
       -- * Generic Data Type
       , Core(..)
       , CoreProg(..)
       , CoreDef(..)
       , defToPair
       , defsToRecBind
       , progToBinds
       , bindsToProg
       -- * Congruence combinators
       -- ** Modguts
       , modGutsT, modGutsR
       -- ** Program
       , progNilT
       , progConsT, progConsAllR, progConsAnyR, progConsOneR
       -- ** Binding Groups
       , nonRecT, nonRecR
       , recT, recAllR, recAnyR, recOneR
       -- ** Recursive Definitions
       , defT, defR
       -- ** Case Alternatives
       , altT, altR
       -- ** Expressions
       , varT
       , litT
       , appT, appAllR, appAnyR, appOneR
       , lamT, lamR
       , letT, letAllR, letAnyR, letOneR
       , caseT, caseAllR, caseAnyR, caseOneR
       , castT, castR
       , tickT, tickR
       , typeT
       , coercionT
       -- ** Composite Congruence Combinators
       , recDefT, recDefAllR, recDefAnyR, recDefOneR
       , letNonRecT, letNonRecAllR, letNonRecAnyR, letNonRecOneR
       , letRecT, letRecAllR, letRecAnyR, letRecOneR
       , letRecDefT, letRecDefAllR, letRecDefAnyR, letRecDefOneR
       , consNonRecT, consNonRecAllR, consNonRecAnyR, consNonRecOneR
       , consRecT, consRecAllR, consRecAnyR, consRecOneR
       , consRecDefT, consRecDefAllR, consRecDefAnyR, consRecDefOneR
       , caseAltT, caseAltAllR, caseAltAnyR, caseAltOneR
       -- * Promotion Combinators
       -- ** Rewrite Promotions
       , promoteModGutsR
       , promoteProgR
       , promoteBindR
       , promoteDefR
       , promoteExprR
       , promoteAltR
       -- ** Translate Promotions
       , promoteModGutsT
       , promoteProgT
       , promoteBindT
       , promoteDefT
       , promoteExprT
       , promoteAltT
       )
where

import GhcPlugins hiding (empty)

import Language.KURE
import Language.KURE.Injection
import Language.KURE.Utilities

import Language.HERMIT.CoreExtra
import Language.HERMIT.Context
import Language.HERMIT.Monad

import Control.Applicative
import qualified Control.Category

import Data.Monoid

---------------------------------------------------------------------

type TranslateH a b = Translate HermitC HermitM a b
type RewriteH a = Rewrite HermitC HermitM a
type LensH a b = Lens HermitC HermitM a b

-- | A synonym for the identity rewrite.  Convienient to avoid importing Control.Category.
idR :: RewriteH a
idR = Control.Category.id

---------------------------------------------------------------------

instance Node Core where
  type Generic Core = Core

  numChildren :: Core -> Int
  numChildren (ModGutsCore x) = numChildren x
  numChildren (ProgCore x)    = numChildren x
  numChildren (BindCore x)    = numChildren x
  numChildren (DefCore x)     = numChildren x
  numChildren (ExprCore x)    = numChildren x
  numChildren (AltCore x)     = numChildren x

-- Defining Walker instances for the Generic type 'Core' is almost entirely automated by KURE.
-- Unfortunately, you still need to pattern match on the 'Core' data type.

instance Walker HermitC HermitM Core where

  childL :: Int -> LensH Core (Generic Core)
  childL n = lens $ translate $ \ c -> \case
          ModGutsCore x -> childLgeneric n c x
          ProgCore x    -> childLgeneric n c x
          BindCore x    -> childLgeneric n c x
          DefCore x     -> childLgeneric n c x
          ExprCore x    -> childLgeneric n c x
          AltCore x     -> childLgeneric n c x

  allT :: Monoid b => TranslateH (Generic Core) b -> TranslateH Core b
  allT t = translate $ \ c -> \case
          ModGutsCore x -> allTgeneric t c x
          ProgCore x    -> allTgeneric t c x
          BindCore x    -> allTgeneric t c x
          DefCore x     -> allTgeneric t c x
          ExprCore x    -> allTgeneric t c x
          AltCore x     -> allTgeneric t c x

  oneT :: TranslateH (Generic Core) b -> TranslateH Core b
  oneT t = translate $ \ c -> \case
          ModGutsCore x -> oneTgeneric t c x
          ProgCore x    -> oneTgeneric t c x
          BindCore x    -> oneTgeneric t c x
          DefCore x     -> oneTgeneric t c x
          ExprCore x    -> oneTgeneric t c x
          AltCore x     -> oneTgeneric t c x

  allR :: RewriteH (Generic Core) -> RewriteH Core
  allR r = rewrite $ \ c -> \case
          ModGutsCore x -> allRgeneric r c x
          ProgCore x    -> allRgeneric r c x
          BindCore x    -> allRgeneric r c x
          DefCore x     -> allRgeneric r c x
          ExprCore x    -> allRgeneric r c x
          AltCore x     -> allRgeneric r c x

  anyR :: RewriteH (Generic Core) -> RewriteH Core
  anyR r = rewrite $ \ c -> \case
          ModGutsCore x -> anyRgeneric r c x
          ProgCore x    -> anyRgeneric r c x
          BindCore x    -> anyRgeneric r c x
          DefCore x     -> anyRgeneric r c x
          ExprCore x    -> anyRgeneric r c x
          AltCore x     -> anyRgeneric r c x

  oneR :: RewriteH (Generic Core) -> RewriteH Core
  oneR r = rewrite $ \ c -> \case
          ModGutsCore x -> oneRgeneric r c x
          ProgCore x    -> oneRgeneric r c x
          BindCore x    -> oneRgeneric r c x
          DefCore x     -> oneRgeneric r c x
          ExprCore x    -> oneRgeneric r c x
          AltCore x     -> oneRgeneric r c x

---------------------------------------------------------------------

instance Injection ModGuts Core where

  inject :: ModGuts -> Core
  inject = ModGutsCore

  retract :: Core -> Maybe ModGuts
  retract (ModGutsCore guts) = Just guts
  retract _                  = Nothing

instance Node ModGuts where
  type Generic ModGuts = Core

  numChildren :: ModGuts -> Int
  numChildren _ = 1

instance Walker HermitC HermitM ModGuts where

  childL :: Int -> LensH ModGuts (Generic ModGuts)
  childL 0 = lens $ modGutsT exposeT (childL1of2 $ \ modguts p -> modguts {mg_binds = progToBinds p})
  childL n = failT (missingChild n)

-- | Translate a module.
--   Slightly different to the other congruence combinators: it passes in *all* of the original to the reconstruction function.
modGutsT :: TranslateH CoreProg a -> (ModGuts -> a -> b) -> TranslateH ModGuts b
modGutsT t f = translate $ \ c modGuts -> f modGuts <$> apply t (c @@ 0) (bindsToProg (mg_binds modGuts))

-- | Rewrite the 'CoreProg' child of a module.
modGutsR :: RewriteH CoreProg -> RewriteH ModGuts
modGutsR r = modGutsT r (\ modguts p -> modguts {mg_binds = progToBinds p})

---------------------------------------------------------------------

instance Injection CoreProg Core where

  inject :: CoreProg -> Core
  inject = ProgCore

  retract :: Core -> Maybe CoreProg
  retract (ProgCore bds) = Just bds
  retract _              = Nothing

instance Node CoreProg where
  type Generic CoreProg = Core

  -- A program is either empty (zero children) or a binding group and the remaining program it scopes over (two children).
  numChildren :: CoreProg -> Int
  numChildren ProgNil        = 0
  numChildren (ProgCons _ _) = 2

instance Walker HermitC HermitM CoreProg where

  childL :: Int -> LensH CoreProg (Generic CoreProg)
  childL 0 = lens $ progConsT exposeT idR (childL0of2 ProgCons)
  childL 1 = lens $ progConsT idR exposeT (childL1of2 ProgCons)
  childL n = failT (missingChild n)

-- | Translate an empty list.
progNilT :: b -> TranslateH CoreProg b
progNilT b = contextfreeT $ \case
                               ProgNil       -> pure b
                               ProgCons _ _  -> fail "no match for ProgNil"

progConsT' :: TranslateH CoreBind a1 -> TranslateH CoreProg a2 -> (HermitM a1 -> HermitM a2 -> HermitM b) -> TranslateH CoreProg b
progConsT' t1 t2 f = translate $ \ c -> \case
                                           ProgCons bd p -> f (apply t1 (c @@ 0) bd) (apply t2 (addBinding bd c @@ 1) p)
                                           _             -> fail "no match for ProgCons"

-- | Translate a program of the form: ('CoreBind' @:@ 'CoreProg')
progConsT :: TranslateH CoreBind a1 -> TranslateH CoreProg a2 -> (a1 -> a2 -> b) -> TranslateH CoreProg b
progConsT t1 t2 f = progConsT' t1 t2 (liftA2 f)

-- | Rewrite all children of a program of the form: ('CoreBind' @:@ 'CoreProg')
progConsAllR :: RewriteH CoreBind -> RewriteH CoreProg -> RewriteH CoreProg
progConsAllR r1 r2 = progConsT r1 r2 ProgCons

-- | Rewrite any children of a program of the form: ('CoreBind' @:@ 'CoreProg')
progConsAnyR :: RewriteH CoreBind -> RewriteH CoreProg -> RewriteH CoreProg
progConsAnyR r1 r2 = progConsT' (attemptR r1) (attemptR r2) (attemptAny2 ProgCons)

-- | Rewrite one child of a program of the form: ('CoreBind' @:@ 'CoreProg')
progConsOneR :: RewriteH CoreBind -> RewriteH CoreProg -> RewriteH CoreProg
progConsOneR r1 r2 = progConsT' (withArgumentT r1) (withArgumentT r2) (attemptOne2 ProgCons)

---------------------------------------------------------------------

instance Injection CoreBind Core where

  inject :: CoreBind -> Core
  inject = BindCore

  retract :: Core -> Maybe CoreBind
  retract (BindCore bnd)  = Just bnd
  retract _               = Nothing

instance Node CoreBind where
  type Generic CoreBind = Core

  numChildren :: CoreBind -> Int
  numChildren (NonRec _ _) = 1
  numChildren (Rec defs)   = length defs

instance Walker HermitC HermitM CoreBind where

  childL :: Int -> LensH CoreBind (Generic CoreBind)
  childL n = lens $ setFailMsg (missingChild n) $
               case n of
                 0 -> nonrec <+ rec
                 _ -> rec

    where
      nonrec = nonRecT exposeT (childL1of2 NonRec)
      rec    = whenM (hasChildT n) $
                  recT (const exposeT) (childLMofN n defsToRecBind)

  allT :: Monoid b => TranslateH (Generic CoreBind) b -> TranslateH CoreBind b
  allT t = nonRecT (extractT t) (\ _ -> id)
        <+ recT (\ _ -> extractT t) mconcat

  oneT :: TranslateH (Generic CoreBind) b -> TranslateH CoreBind b
  oneT t = nonRecT (extractT t) (\ _ -> id)
        <+ recT' (\ _ -> extractT t) catchesM

  allR :: RewriteH (Generic CoreBind) -> RewriteH CoreBind
  allR r = nonRecR (extractR r)
        <+ recAllR (\ _ -> extractR r)

  anyR :: RewriteH (Generic CoreBind) -> RewriteH CoreBind
  anyR r = nonRecR (extractR r)
        <+ recAnyR (\ _ -> extractR r)

  oneR :: RewriteH (Generic CoreBind) -> RewriteH CoreBind
  oneR r = nonRecR (extractR r)
        <+ recOneR (\ _ -> extractR r)

-- | Translate a binding group of the form: @NonRec@ 'Id' 'CoreExpr'
nonRecT :: TranslateH CoreExpr a -> (Id -> a -> b) -> TranslateH CoreBind b
nonRecT t f = translate $ \ c -> \case
                                    NonRec v e -> f v <$> apply t (c @@ 0) e
                                    _          -> fail "not NonRec constructor"

-- | Rewrite the 'CoreExpr' child of a binding group of the form: @NonRec@ 'Id' 'CoreExpr'
nonRecR :: RewriteH CoreExpr -> RewriteH CoreBind
nonRecR r = nonRecT r NonRec

recT' :: (Int -> TranslateH CoreDef a) -> ([HermitM a] -> HermitM b) -> TranslateH CoreBind b
recT' t f = translate $ \ c -> \case
         Rec bds -> -- Notice how we add the scoping bindings here *before* descending into each individual definition.
                    let c' = addBinding (Rec bds) c
                     in f [ apply (t n) (c' @@ n) (Def v e) -- here we convert from (Id,CoreExpr) to CoreDef
                          | ((v,e),n) <- zip bds [0..]
                          ]
         _       -> fail "not Rec constructor"

-- | Translate a binding group of the form: @Rec@ ['CoreDef']
recT :: (Int -> TranslateH CoreDef a) -> ([a] -> b) -> TranslateH CoreBind b
recT ts f = recT' ts (fmap f . sequence)

-- | Rewrite all children of a binding group of the form: @Rec@ ['CoreDef']
recAllR :: (Int -> RewriteH CoreDef) -> RewriteH CoreBind
recAllR rs = recT rs defsToRecBind

-- | Rewrite any children of a binding group of the form: @Rec@ ['CoreDef']
recAnyR :: (Int -> RewriteH CoreDef) -> RewriteH CoreBind
recAnyR rs = recT' (attemptR . rs) (attemptAnyN defsToRecBind)

-- | Rewrite one child of a binding group of the form: @Rec@ ['CoreDef']
recOneR :: (Int -> RewriteH CoreDef) -> RewriteH CoreBind
recOneR rs = recT' (withArgumentT . rs) (attemptOneN defsToRecBind)

---------------------------------------------------------------------

instance Injection CoreDef Core where

  inject :: CoreDef -> Core
  inject = DefCore

  retract :: Core -> Maybe CoreDef
  retract (DefCore def) = Just def
  retract _             = Nothing

instance Node CoreDef where
  type Generic CoreDef = Core

  numChildren :: CoreDef -> Int
  numChildren _ = 1

instance Walker HermitC HermitM CoreDef where

  childL :: Int -> LensH CoreDef (Generic CoreDef)
  childL 0 = lens $ defT exposeT (childL1of2 Def)
  childL n = failT (missingChild n)

-- | Translate a recursive definition of the form: @Def@ 'Id' 'CoreExpr'
defT :: TranslateH CoreExpr a -> (Id -> a -> b) -> TranslateH CoreDef b
defT t f = translate $ \ c (Def v e) -> f v <$> apply t (c @@ 0) e

-- | Rewrite the 'CoreExpr' child of a recursive definition of the form: @Def@ 'Id' 'CoreExpr'
defR :: RewriteH CoreExpr -> RewriteH CoreDef
defR r = defT r Def

---------------------------------------------------------------------

instance Injection CoreAlt Core where

  inject :: CoreAlt -> Core
  inject = AltCore

  retract :: Core -> Maybe CoreAlt
  retract (AltCore expr) = Just expr
  retract _              = Nothing

instance Node CoreAlt where
  type Generic CoreAlt = Core

  numChildren :: CoreAlt -> Int
  numChildren _ = 1

instance Walker HermitC HermitM CoreAlt where

  childL :: Int -> LensH CoreAlt (Generic CoreAlt)
  childL 0 = lens $ altT exposeT (childL2of3 (,,))
  childL n = failT (missingChild n)

-- | Translate a case alternative of the form: ('AltCon', ['Id'], 'CoreExpr')
altT :: TranslateH CoreExpr a -> (AltCon -> [Id] -> a -> b) -> TranslateH CoreAlt b
altT t f = translate $ \ c (con,bs,e) -> f con bs <$> apply t (addAltBindings bs c @@ 0) e

-- | Rewrite the 'CoreExpr' child of a case alternative of the form: ('AltCon', 'Id', 'CoreExpr')
altR :: RewriteH CoreExpr -> RewriteH CoreAlt
altR r = altT r (,,)

---------------------------------------------------------------------

instance Injection CoreExpr Core where

  inject :: CoreExpr -> Core
  inject = ExprCore

  retract :: Core -> Maybe CoreExpr
  retract (ExprCore expr) = Just expr
  retract _               = Nothing

instance Node CoreExpr where
  type Generic CoreExpr = Core

  numChildren :: CoreExpr -> Int
  numChildren (Var _)         = 0
  numChildren (Lit _)         = 0
  numChildren (App _ _)       = 2
  numChildren (Lam _ _)       = 1
  numChildren (Let _ _)       = 2
  numChildren (Case _ _ _ es) = 1 + length es
  numChildren (Cast _ _)      = 1
  numChildren (Tick _ _)      = 1
  numChildren (Type _)        = 0
  numChildren (Coercion _)    = 0

instance Walker HermitC HermitM CoreExpr where

  childL :: Int -> LensH CoreExpr (Generic CoreExpr)
  childL n = lens $ setFailMsg (missingChild n) $
               case n of
                 0  ->    appT  exposeT idR         (childL0of2 App)
                       <+ lamT  exposeT             (childL1of2 Lam)
                       <+ letT  exposeT idR         (childL0of2 Let)
                       <+ caseT exposeT (const idR) (childL0of4 Case)
                       <+ castT exposeT             (childL0of2 Cast)
                       <+ tickT exposeT             (childL1of2 Tick)

                 1  ->    appT idR exposeT (childL1of2 App)
                       <+ letT idR exposeT (childL1of2 Let)
                       <+ caseChooseL

                 _  ->    caseChooseL
     where
       -- Note we use index (n-1) because 0 refers to the expression being scrutinised.
       caseChooseL = whenM (hasChildT n) $
                           caseT idR (const exposeT) (\ e v t -> childLMofN (n-1) (Case e v t))

  allT :: Monoid b => TranslateH (Generic CoreExpr) b -> TranslateH CoreExpr b
  allT t = varT (\ _ -> mempty)
        <+ litT (\ _ -> mempty)
        <+ appT (extractT t) (extractT t) mappend
        <+ lamT (extractT t) (\ _ -> id)
        <+ letT (extractT t) (extractT t) mappend
        <+ caseT (extractT t) (\ _ -> extractT t) (\ r _ _ rs -> mconcat (r:rs))
        <+ castT (extractT t) const
        <+ tickT (extractT t) (\ _ -> id)
        <+ typeT (\ _ -> mempty)
        <+ coercionT (\ _ -> mempty)

  oneT :: TranslateH (Generic CoreExpr) b -> TranslateH CoreExpr b
  oneT t = appT' (extractT t) (extractT t) (<<+)
        <+ lamT (extractT t) (\ _ -> id)
        <+ letT' (extractT t) (extractT t) (<<+)
        <+ caseT' (extractT t) (\ _ -> extractT t) (\ _ _ r rs -> catchesM (r:rs))
        <+ castT (extractT t) const
        <+ tickT (extractT t) (\ _ -> id)

  allR :: RewriteH (Generic CoreExpr) -> RewriteH CoreExpr
  allR r = varT Var
        <+ litT Lit
        <+ appAllR (extractR r) (extractR r)
        <+ lamR (extractR r)
        <+ letAllR (extractR r) (extractR r)
        <+ caseAllR (extractR r) (\ _ -> extractR r)
        <+ castR (extractR r)
        <+ tickR (extractR r)
        <+ typeT Type
        <+ coercionT Coercion

  anyR :: RewriteH (Generic CoreExpr) -> RewriteH CoreExpr
  anyR r = appAnyR (extractR r) (extractR r)
        <+ lamR (extractR r)
        <+ letAnyR (extractR r) (extractR r)
        <+ caseAnyR (extractR r) (\ _ -> extractR r)
        <+ castR (extractR r)
        <+ tickR (extractR r)
        <+ fail "anyR failed"

  oneR :: RewriteH (Generic CoreExpr) -> RewriteH CoreExpr
  oneR r = appOneR (extractR r) (extractR r)
        <+ lamR (extractR r)
        <+ letOneR (extractR r) (extractR r)
        <+ caseOneR (extractR r) (\ _ -> extractR r)
        <+ castR (extractR r)
        <+ tickR (extractR r)
        <+ fail "oneR failed"

---------------------------------------------------------------------

-- | Translate an expression of the form: @Var@ 'Id'
varT :: (Id -> b) -> TranslateH CoreExpr b
varT f = contextfreeT $ \case
                           Var v -> pure (f v)
                           _     -> fail "no match for Var"

-- | Translate an expression of the form: @Lit@ 'Literal'
litT :: (Literal -> b) -> TranslateH CoreExpr b
litT f = contextfreeT $ \case
                           Lit x -> pure (f x)
                           _     -> fail "no match for Lit"


appT' :: TranslateH CoreExpr a1 -> TranslateH CoreExpr a2 -> (HermitM a1 -> HermitM a2 -> HermitM b) -> TranslateH CoreExpr b
appT' t1 t2 f = translate $ \ c -> \case
                                      App e1 e2 -> f (apply t1 (c @@ 0) e1) (apply t2 (c @@ 1) e2)
                                      _         -> fail "no match for App"

-- | Translate an expression of the form: @App@ 'CoreExpr' 'CoreExpr'
appT :: TranslateH CoreExpr a1 -> TranslateH CoreExpr a2 -> (a1 -> a2 -> b) -> TranslateH CoreExpr b
appT t1 t2 = appT' t1 t2 . liftA2

-- | Rewrite all children of an expression of the form: @App@ 'CoreExpr' 'CoreExpr'
appAllR :: RewriteH CoreExpr -> RewriteH CoreExpr -> RewriteH CoreExpr
appAllR r1 r2 = appT r1 r2 App

-- | Rewrite any children of an expression of the form: @App@ 'CoreExpr' 'CoreExpr'
appAnyR :: RewriteH CoreExpr -> RewriteH CoreExpr -> RewriteH CoreExpr
appAnyR r1 r2 = appT' (attemptR r1) (attemptR r2) (attemptAny2 App)

-- | Rewrite one child of an expression of the form: @App@ 'CoreExpr' 'CoreExpr'
appOneR :: RewriteH CoreExpr -> RewriteH CoreExpr -> RewriteH CoreExpr
appOneR r1 r2 = appT' (withArgumentT r1) (withArgumentT r2) (attemptOne2 App)

-- | Translate an expression of the form: @Lam@ 'Id' 'CoreExpr'
lamT :: TranslateH CoreExpr a -> (Id -> a -> b) -> TranslateH CoreExpr b
lamT t f = translate $ \ c -> \case
                                 Lam b e -> f b <$> apply t (addLambdaBinding b c @@ 0) e
                                 _       -> fail "no match for Lam"

-- | Rewrite the 'CoreExpr' child of an expression of the form: @Lam@ 'Id' 'CoreExpr'
lamR :: RewriteH CoreExpr -> RewriteH CoreExpr
lamR r = lamT r Lam


letT' :: TranslateH CoreBind a1 -> TranslateH CoreExpr a2 -> (HermitM a1 -> HermitM a2 -> HermitM b) -> TranslateH CoreExpr b
letT' t1 t2 f = translate $ \ c -> \case
        Let bds e -> f (apply t1 (c @@ 0) bds) (apply t2 (addBinding bds c @@ 1) e)
                -- use *original* env, because the bindings are self-binding,
                -- if they are recursive. See recT'.
        _         -> fail "no match for Let"

-- | Translate an expression of the form: @Let@ 'CoreBind' 'CoreExpr'
letT :: TranslateH CoreBind a1 -> TranslateH CoreExpr a2 -> (a1 -> a2 -> b) -> TranslateH CoreExpr b
letT t1 t2 = letT' t1 t2 . liftA2

-- | Rewrite all children of an expression of the form: @Let@ 'CoreBind' 'CoreExpr'
letAllR :: RewriteH CoreBind -> RewriteH CoreExpr -> RewriteH CoreExpr
letAllR r1 r2 = letT r1 r2 Let

-- | Rewrite any children of an expression of the form: @Let@ 'CoreBind' 'CoreExpr'
letAnyR :: RewriteH CoreBind -> RewriteH CoreExpr -> RewriteH CoreExpr
letAnyR r1 r2 = letT' (attemptR r1) (attemptR r2) (attemptAny2 Let)

-- | Rewrite one child of an expression of the form: @Let@ 'CoreBind' 'CoreExpr'
letOneR :: RewriteH CoreBind -> RewriteH CoreExpr -> RewriteH CoreExpr
letOneR r1 r2 = letT' (withArgumentT r1) (withArgumentT r2) (attemptOne2 Let)


caseT' :: TranslateH CoreExpr a1 -> (Int -> TranslateH CoreAlt a2) -> (Id -> Type -> HermitM a1 -> [HermitM a2] -> HermitM b) -> TranslateH CoreExpr b
caseT' t ts f = translate $ \ c -> \case
         Case e b ty alts -> f b ty (apply t (c @@ 0) e) $ [ apply (ts n) (addCaseBinding (b,e,alt) c @@ (n+1)) alt
                                                           | (alt,n) <- zip alts [0..]
                                                           ]
         _                -> fail "no match for Case"

-- | Translate an expression of the form: @Case@ 'CoreExpr' 'Id' 'Type' ['CoreAlt']
caseT :: TranslateH CoreExpr a1 -> (Int -> TranslateH CoreAlt a2) -> (a1 -> Id -> Type -> [a2] -> b) -> TranslateH CoreExpr b
caseT t ts f = caseT' t ts (\ b ty me malts -> f <$> me <*> pure b <*> pure ty <*> sequence malts)

-- | Rewrite all children of an expression of the form: @Case@ 'CoreExpr' 'Id' 'Type' ['CoreAlt']
caseAllR :: RewriteH CoreExpr -> (Int -> RewriteH CoreAlt) -> RewriteH CoreExpr
caseAllR r rs = caseT r rs Case

-- | Rewrite any children of an expression of the form: @Case@ 'CoreExpr' 'Id' 'Type' ['CoreAlt']
caseAnyR :: RewriteH CoreExpr -> (Int -> RewriteH CoreAlt) -> RewriteH CoreExpr
caseAnyR r rs = caseT' (attemptR r) (attemptR . rs) (\ b ty -> attemptAny1N (\ e -> Case e b ty))

-- | Rewrite one child of an expression of the form: @Case@ 'CoreExpr' 'Id' 'Type' ['CoreAlt']
caseOneR :: RewriteH CoreExpr -> (Int -> RewriteH CoreAlt) -> RewriteH CoreExpr
caseOneR r rs = caseT' (withArgumentT r) (withArgumentT . rs) (\ b ty -> attemptOne1N (\ e -> Case e b ty))

-- | Translate an expression of the form: @Cast@ 'CoreExpr' 'Coercion'
castT :: TranslateH CoreExpr a -> (a -> Coercion -> b) -> TranslateH CoreExpr b
castT t f = translate $ \ c -> \case
                                  Cast e cast -> f <$> apply t (c @@ 0) e <*> pure cast
                                  _           -> fail "no match for Cast"

-- | Rewrite the 'CoreExpr' child of an expression of the form: @Cast@ 'CoreExpr' 'Coercion'
castR :: RewriteH CoreExpr -> RewriteH CoreExpr
castR r = castT r Cast

-- | Translate an expression of the form: @Tick@ 'CoreTickish' 'CoreExpr'
tickT :: TranslateH CoreExpr a -> (CoreTickish -> a -> b) -> TranslateH CoreExpr b
tickT t f = translate $ \ c -> \case
        Tick tk e -> f tk <$> apply t (c @@ 0) e
        _         -> fail "no match for Tick"

-- | Rewrite the 'CoreExpr' child of an expression of the form: @Tick@ 'CoreTickish' 'CoreExpr'
tickR :: RewriteH CoreExpr -> RewriteH CoreExpr
tickR r = tickT r Tick

-- | Translate an expression of the form: @Type@ 'Type'
typeT :: (Type -> b) -> TranslateH CoreExpr b
typeT f = contextfreeT $ \case
                            Type t -> pure (f t)
                            _      -> fail "no match for Type"

-- | Translate an expression of the form: @Coercion@ 'Coercion'
coercionT :: (Coercion -> b) -> TranslateH CoreExpr b
coercionT f = contextfreeT $ \case
                                Coercion co -> pure (f co)
                                _           -> fail "no match for Coercion"

---------------------------------------------------------------------

-- Some composite congruence combinators to export.

-- | Translate a binding group of the form: @Rec@ [('Id', 'CoreExpr')]
recDefT :: (Int -> TranslateH CoreExpr a1) -> ([(Id,a1)] -> b) -> TranslateH CoreBind b
recDefT ts = recT (\ n -> defT (ts n) (,))

-- | Rewrite all children of a binding group of the form: @Rec@ [('Id', 'CoreExpr')]
recDefAllR :: (Int -> RewriteH CoreExpr) -> RewriteH CoreBind
recDefAllR rs = recAllR (\ n -> defR (rs n))

-- | Rewrite any children of a binding group of the form: @Rec@ [('Id', 'CoreExpr')]
recDefAnyR :: (Int -> RewriteH CoreExpr) -> RewriteH CoreBind
recDefAnyR rs = recAnyR (\ n -> defR (rs n))

-- | Rewrite one child of a binding group of the form: @Rec@ [('Id', 'CoreExpr')]
recDefOneR :: (Int -> RewriteH CoreExpr) -> RewriteH CoreBind
recDefOneR rs = recOneR (\ n -> defR (rs n))


-- | Translate a program of the form: (@NonRec@ 'Id' 'CoreExpr') @:@ 'CoreProg'
consNonRecT :: TranslateH CoreExpr a1 -> TranslateH CoreProg a2 -> (Id -> a1 -> a2 -> b) -> TranslateH CoreProg b
consNonRecT t1 t2 f = progConsT (nonRecT t1 (,)) t2 (uncurry f)

-- | Rewrite all children of an expression of the form: (@NonRec@ 'Id' 'CoreExpr') @:@ 'CoreProg'
consNonRecAllR :: RewriteH CoreExpr -> RewriteH CoreProg -> RewriteH CoreProg
consNonRecAllR r1 r2 = progConsAllR (nonRecR r1) r2

-- | Rewrite any children of an expression of the form: (@NonRec@ 'Id' 'CoreExpr') @:@ 'CoreProg'
consNonRecAnyR :: RewriteH CoreExpr -> RewriteH CoreProg -> RewriteH CoreProg
consNonRecAnyR r1 r2 = progConsAnyR (nonRecR r1) r2

-- | Rewrite one child of an expression of the form: (@NonRec@ 'Id' 'CoreExpr') @:@ 'CoreProg'
consNonRecOneR :: RewriteH CoreExpr -> RewriteH CoreProg -> RewriteH CoreProg
consNonRecOneR r1 r2 = progConsOneR (nonRecR r1) r2


-- | Translate an expression of the form: (@Rec@ ['CoreDef']) @:@ 'CoreProg'
consRecT :: (Int -> TranslateH CoreDef a1) -> TranslateH CoreProg a2 -> ([a1] -> a2 -> b) -> TranslateH CoreProg b
consRecT ts t = progConsT (recT ts id) t

-- | Rewrite all children of an expression of the form: (@Rec@ ['CoreDef']) @:@ 'CoreProg'
consRecAllR :: (Int -> RewriteH CoreDef) -> RewriteH CoreProg -> RewriteH CoreProg
consRecAllR rs r = progConsAllR (recAllR rs) r

-- | Rewrite any children of an expression of the form: (@Rec@ ['CoreDef']) @:@ 'CoreProg'
consRecAnyR :: (Int -> RewriteH CoreDef) -> RewriteH CoreProg -> RewriteH CoreProg
consRecAnyR rs r = progConsAnyR (recAnyR rs) r

-- | Rewrite one child of an expression of the form: (@Rec@ ['CoreDef']) @:@ 'CoreProg'
consRecOneR :: (Int -> RewriteH CoreDef) -> RewriteH CoreProg -> RewriteH CoreProg
consRecOneR rs r = progConsOneR (recOneR rs) r


-- | Translate an expression of the form: (@Rec@ [('Id', 'CoreExpr')]) @:@ 'CoreProg'
consRecDefT :: (Int -> TranslateH CoreExpr a1) -> TranslateH CoreProg a2 -> ([(Id,a1)] -> a2 -> b) -> TranslateH CoreProg b
consRecDefT ts t = consRecT (\ n -> defT (ts n) (,)) t

-- | Rewrite all children of an expression of the form: (@Rec@ [('Id', 'CoreExpr')]) @:@ 'CoreProg'
consRecDefAllR :: (Int -> RewriteH CoreExpr) -> RewriteH CoreProg -> RewriteH CoreProg
consRecDefAllR rs r = consRecAllR (\ n -> defR (rs n)) r

-- | Rewrite any children of an expression of the form: (@Rec@ [('Id', 'CoreExpr')]) @:@ 'CoreProg'
consRecDefAnyR :: (Int -> RewriteH CoreExpr) -> RewriteH CoreProg -> RewriteH CoreProg
consRecDefAnyR rs r = consRecAnyR (\ n -> defR (rs n)) r

-- | Rewrite one child of an expression of the form: (@Rec@ [('Id', 'CoreExpr')]) @:@ 'CoreProg'
consRecDefOneR :: (Int -> RewriteH CoreExpr) -> RewriteH CoreProg -> RewriteH CoreProg
consRecDefOneR rs r = consRecOneR (\ n -> defR (rs n)) r


-- | Translate an expression of the form: @Let@ (@NonRec@ 'Id' 'CoreExpr') 'CoreExpr'
letNonRecT :: TranslateH CoreExpr a1 -> TranslateH CoreExpr a2 -> (Id -> a1 -> a2 -> b) -> TranslateH CoreExpr b
letNonRecT t1 t2 f = letT (nonRecT t1 (,)) t2 (uncurry f)

-- | Rewrite all children of an expression of the form: @Let@ (@NonRec@ 'Id' 'CoreExpr') 'CoreExpr'
letNonRecAllR :: RewriteH CoreExpr -> RewriteH CoreExpr -> RewriteH CoreExpr
letNonRecAllR r1 r2 = letAllR (nonRecR r1) r2

-- | Rewrite any children of an expression of the form: @Let@ (@NonRec@ 'Id' 'CoreExpr') 'CoreExpr'
letNonRecAnyR :: RewriteH CoreExpr -> RewriteH CoreExpr -> RewriteH CoreExpr
letNonRecAnyR r1 r2 = letAnyR (nonRecR r1) r2

-- | Rewrite one child of an expression of the form: @Let@ (@NonRec@ 'Id' 'CoreExpr') 'CoreExpr'
letNonRecOneR :: RewriteH CoreExpr -> RewriteH CoreExpr -> RewriteH CoreExpr
letNonRecOneR r1 r2 = letOneR (nonRecR r1) r2


-- | Translate an expression of the form: @Let@ (@Rec@ ['CoreDef']) 'CoreExpr'
letRecT :: (Int -> TranslateH CoreDef a1) -> TranslateH CoreExpr a2 -> ([a1] -> a2 -> b) -> TranslateH CoreExpr b
letRecT ts t = letT (recT ts id) t

-- | Rewrite all children of an expression of the form: @Let@ (@Rec@ ['CoreDef']) 'CoreExpr'
letRecAllR :: (Int -> RewriteH CoreDef) -> RewriteH CoreExpr -> RewriteH CoreExpr
letRecAllR rs r = letAllR (recAllR rs) r

-- | Rewrite any children of an expression of the form: @Let@ (@Rec@ ['CoreDef']) 'CoreExpr'
letRecAnyR :: (Int -> RewriteH CoreDef) -> RewriteH CoreExpr -> RewriteH CoreExpr
letRecAnyR rs r = letAnyR (recAnyR rs) r

-- | Rewrite one child of an expression of the form: @Let@ (@Rec@ ['CoreDef']) 'CoreExpr'
letRecOneR :: (Int -> RewriteH CoreDef) -> RewriteH CoreExpr -> RewriteH CoreExpr
letRecOneR rs r = letOneR (recOneR rs) r


-- | Translate an expression of the form: @Let@ (@Rec@ [('Id', 'CoreExpr')]) 'CoreExpr'
letRecDefT :: (Int -> TranslateH CoreExpr a1) -> TranslateH CoreExpr a2 -> ([(Id,a1)] -> a2 -> b) -> TranslateH CoreExpr b
letRecDefT ts t = letRecT (\ n -> defT (ts n) (,)) t

-- | Rewrite all children of an expression of the form: @Let@ (@Rec@ [('Id', 'CoreExpr')]) 'CoreExpr'
letRecDefAllR :: (Int -> RewriteH CoreExpr) -> RewriteH CoreExpr -> RewriteH CoreExpr
letRecDefAllR rs r = letRecAllR (\ n -> defR (rs n)) r

-- | Rewrite any children of an expression of the form: @Let@ (@Rec@ [('Id', 'CoreExpr')]) 'CoreExpr'
letRecDefAnyR :: (Int -> RewriteH CoreExpr) -> RewriteH CoreExpr -> RewriteH CoreExpr
letRecDefAnyR rs r = letRecAnyR (\ n -> defR (rs n)) r

-- | Rewrite one child of an expression of the form: @Let@ (@Rec@ [('Id', 'CoreExpr')]) 'CoreExpr'
letRecDefOneR :: (Int -> RewriteH CoreExpr) -> RewriteH CoreExpr -> RewriteH CoreExpr
letRecDefOneR rs r = letRecOneR (\ n -> defR (rs n)) r


-- | Translate an expression of the form: @Case@ 'CoreExpr' 'Id' 'Type' [('AltCon', ['Id'], 'CoreExpr')]
caseAltT :: TranslateH CoreExpr a1 -> (Int -> TranslateH CoreExpr a2) -> (a1 -> Id -> Type -> [(AltCon,[Id],a2)] -> b) -> TranslateH CoreExpr b
caseAltT t ts = caseT t (\ n -> altT (ts n) (,,))

-- | Rewrite all children of an expression of the form: @Case@ 'CoreExpr' 'Id' 'Type' [('AltCon', ['Id'], 'CoreExpr')]
caseAltAllR :: RewriteH CoreExpr -> (Int -> RewriteH CoreExpr) -> RewriteH CoreExpr
caseAltAllR t ts = caseAllR t (\ n -> altR (ts n))

-- | Rewrite any children of an expression of the form: @Case@ 'CoreExpr' 'Id' 'Type' [('AltCon', ['Id'], 'CoreExpr')]
caseAltAnyR :: RewriteH CoreExpr -> (Int -> RewriteH CoreExpr) -> RewriteH CoreExpr
caseAltAnyR t ts = caseAnyR t (\ n -> altR (ts n))

-- | Rewrite one child of an expression of the form: @Case@ 'CoreExpr' 'Id' 'Type' [('AltCon', ['Id'], 'CoreExpr')]
caseAltOneR :: RewriteH CoreExpr -> (Int -> RewriteH CoreExpr) -> RewriteH CoreExpr
caseAltOneR t ts = caseOneR t (\ n -> altR (ts n))

---------------------------------------------------------------------

-- | Promote a rewrite on 'ModGuts' to a rewrite on 'Core'.
promoteModGutsR :: RewriteH ModGuts -> RewriteH Core
promoteModGutsR = promoteWithFailMsgR "This rewrite can only succeed at the module level."

-- | Promote a rewrite on 'CoreProg' to a rewrite on 'Core'.
promoteProgR :: RewriteH CoreProg -> RewriteH Core
promoteProgR = promoteWithFailMsgR "This rewrite can only succeed at program nodes (the top-level)."

-- | Promote a rewrite on 'CoreBind' to a rewrite on 'Core'.
promoteBindR :: RewriteH CoreBind -> RewriteH Core
promoteBindR = promoteWithFailMsgR "This rewrite can only succeed at binding group nodes."

-- | Promote a rewrite on 'CoreDef' to a rewrite on 'Core'.
promoteDefR :: RewriteH CoreDef -> RewriteH Core
promoteDefR = promoteWithFailMsgR "This rewrite can only succeed at recursive definition nodes."

-- | Promote a rewrite on 'CoreAlt' to a rewrite on 'Core'.
promoteAltR :: RewriteH CoreAlt -> RewriteH Core
promoteAltR = promoteWithFailMsgR "This rewrite can only succeed at case alternative nodes."

-- | Promote a rewrite on 'CoreExpr' to a rewrite on 'Core'.
promoteExprR :: RewriteH CoreExpr -> RewriteH Core
promoteExprR = promoteWithFailMsgR "This rewrite can only succeed at expression nodes."

---------------------------------------------------------------------

-- | Promote a translate on 'ModGuts' to a translate on 'Core'.
promoteModGutsT :: TranslateH ModGuts b -> TranslateH Core b
promoteModGutsT = promoteWithFailMsgT "This translate can only succeed at the module level."

-- | Promote a translate on 'CoreProg' to a translate on 'Core'.
promoteProgT :: TranslateH CoreProg b -> TranslateH Core b
promoteProgT = promoteWithFailMsgT "This translate can only succeed at program nodes (the top-level)."

-- | Promote a translate on 'CoreBind' to a translate on 'Core'.
promoteBindT :: TranslateH CoreBind b -> TranslateH Core b
promoteBindT = promoteWithFailMsgT "This translate can only succeed at binding group nodes."

-- | Promote a translate on 'CoreDef' to a translate on 'Core'.
promoteDefT :: TranslateH CoreDef b -> TranslateH Core b
promoteDefT = promoteWithFailMsgT "This translate can only succeed at recursive definition nodes."

-- | Promote a translate on 'CoreAlt' to a translate on 'Core'.
promoteAltT :: TranslateH CoreAlt b -> TranslateH Core b
promoteAltT = promoteWithFailMsgT "This translate can only succeed at case alternative nodes."

-- | Promote a translate on 'CoreExpr' to a translate on 'Core'.
promoteExprT :: TranslateH CoreExpr b -> TranslateH Core b
promoteExprT = promoteWithFailMsgT "This translate can only succeed at expression nodes."

---------------------------------------------------------------------
