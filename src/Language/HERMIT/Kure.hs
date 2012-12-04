{-# LANGUAGE MultiParamTypeClasses, TypeFamilies, FlexibleInstances, FlexibleContexts, TupleSections, LambdaCase, InstanceSigs #-}

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

import Language.HERMIT.Core
import Language.HERMIT.Context
import Language.HERMIT.Monad

import Control.Applicative
import qualified Control.Category

import Data.Monoid

---------------------------------------------------------------------

type TranslateH a b = Translate HermitC HermitM a b
type RewriteH a = Rewrite HermitC HermitM a
type LensH a b = Lens HermitC HermitM a b

-- | A synonym for the identity rewrite.  Convienient to avoid importing Control.Category and hiding the Prelude id.
idR :: RewriteH a
idR = Control.Category.id

---------------------------------------------------------------------

instance Injection ModGuts Core where

  inject :: ModGuts -> Core
  inject = ModGutsCore

  retract :: Core -> Maybe ModGuts
  retract (ModGutsCore guts) = Just guts
  retract _                  = Nothing


instance Injection CoreProg Core where

  inject :: CoreProg -> Core
  inject = ProgCore

  retract :: Core -> Maybe CoreProg
  retract (ProgCore bds) = Just bds
  retract _              = Nothing


instance Injection CoreBind Core where

  inject :: CoreBind -> Core
  inject = BindCore

  retract :: Core -> Maybe CoreBind
  retract (BindCore bnd)  = Just bnd
  retract _               = Nothing


instance Injection CoreDef Core where

  inject :: CoreDef -> Core
  inject = DefCore

  retract :: Core -> Maybe CoreDef
  retract (DefCore def) = Just def
  retract _             = Nothing


instance Injection CoreAlt Core where

  inject :: CoreAlt -> Core
  inject = AltCore

  retract :: Core -> Maybe CoreAlt
  retract (AltCore expr) = Just expr
  retract _              = Nothing


instance Injection CoreExpr Core where

  inject :: CoreExpr -> Core
  inject = ExprCore

  retract :: Core -> Maybe CoreExpr
  retract (ExprCore expr) = Just expr
  retract _               = Nothing

---------------------------------------------------------------------

instance Node Core where

  numChildren :: Core -> Int
  numChildren (ModGutsCore _) = 1
  numChildren (ProgCore p)    = -- A program is either empty (zero children) or a binding group and the remaining program it scopes over (two children).
                                case p of
                                  ProgNil       -> 0
                                  ProgCons _ _  -> 2
  numChildren (BindCore bnd)  = case bnd of
                                  NonRec _ _  -> 1
                                  Rec defs    -> length defs
  numChildren (DefCore _)     = 1
  numChildren (AltCore _)     = 1
  numChildren (ExprCore e)    = case e of
                                  Var _          -> 0
                                  Lit _          -> 0
                                  App _ _        -> 2
                                  Lam _ _        -> 1
                                  Let _ _        -> 2
                                  Case _ _ _ es  -> 1 + length es
                                  Cast _ _       -> 1
                                  Tick _ _       -> 1
                                  Type _         -> 0
                                  Coercion _     -> 0

---------------------------------------------------------------------

instance Walker HermitC HermitM Core where

  childL :: Int -> LensH Core Core
  childL n = lens $ flip (ifM $ hasChildT n) (fail $ missingChild n) $ translate $ \ c -> \case
          ModGutsCore guts -> apply childLmodguts c guts
          ProgCore p       -> apply childLprog c p
          BindCore bn      -> apply childLbind c bn
          DefCore def      -> apply childLdef c def
          AltCore alt      -> apply childLalt c alt
          ExprCore e       -> apply childLexpr c e
    where
      childLmodguts :: TranslateH ModGuts ((HermitC,Core) , Core -> HermitM Core)
      childLmodguts = modGutsT exposeT (childL1of2 $ \ guts p -> guts {mg_binds = progToBinds p})

      childLprog :: TranslateH CoreProg ((HermitC,Core) , Core -> HermitM Core)
      childLprog = case n of
                     0  -> progConsT exposeT idR (childL0of2 ProgCons)
                     1  -> progConsT idR exposeT (childL1of2 ProgCons)
                     _  -> error "This shouldn't happen.  Cannot occur due to 'hasChild' check above."

      childLbind :: TranslateH CoreBind ((HermitC,Core) , Core -> HermitM Core)
      childLbind = let nonrec = nonRecT exposeT (childL1of2 NonRec)
                       rec    = recT (const exposeT) (childLMofN n defsToRecBind)
                    in case n of
                         0 -> nonrec <+ rec
                         _ -> rec

      childLdef :: TranslateH CoreDef ((HermitC,Core) , Core -> HermitM Core)
      childLdef = defT exposeT (childL1of2 Def)

      childLalt :: TranslateH CoreAlt ((HermitC,Core) , Core -> HermitM Core)
      childLalt = altT exposeT (childL2of3 (,,))

      childLexpr :: TranslateH CoreExpr ((HermitC,Core) , Core -> HermitM Core)
      childLexpr = let -- Note we use index (n-1) because 0 refers to the expression being scrutinised.
                       caseChooseL = caseT idR (const exposeT) (\ e v t -> childLMofN (n-1) (Case e v t))
                    in case n of
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

  allT :: Monoid b => TranslateH Core b -> TranslateH Core b
  allT t = let allTrec  = recT (\ _ -> extractT t) mconcat
               allTcase = caseT (extractT t) (\ _ -> extractT t) (\ r _ _ rs -> mconcat (r:rs))
            in translate $ \ c -> \case
                BindCore bnd@(Rec _)       -> prefixFailMsg "allT failed for Rec: " $ apply allTrec c bnd
                ExprCore e@(Case _ _ _ _)  -> prefixFailMsg "allT failed for Case: " $ apply allTcase c e
                core                       -> apply (allTdefault t) c core

  oneT :: TranslateH Core b -> TranslateH Core b
  oneT t = let oneTrec  = recT' (\ _ -> extractT t) catchesM
               oneTcase = caseT' (extractT t) (\ _ -> extractT t) (\ _ _ r rs -> catchesM (r:rs))
            in translate $ \ c -> \case
                BindCore bnd@(Rec _)       -> setFailMsg "oneT failed for Rec" $ apply oneTrec c bnd
                ExprCore e@(Case _ _ _ _)  -> setFailMsg "oneT failed for Case" $ apply oneTcase c e
                core                       -> apply (oneTdefault t) c core

  allR :: RewriteH Core -> RewriteH Core
  allR r = let allRrec  = recAllR (\ _ -> extractR r)
               allRcase = caseAllR (extractR r) (\ _ -> extractR r)
            in rewrite $ \ c -> \case
                 BindCore bnd@(Rec _)       -> prefixFailMsg "allR failed for Rec: " $ inject <$> apply allRrec c bnd
                 ExprCore e@(Case _ _ _ _)  -> prefixFailMsg "allR failed for Case: " $ inject <$> apply allRcase c e
                 core                       -> apply (allRdefault r) c core

  anyR :: RewriteH Core -> RewriteH Core
  anyR r = let anyRrec  = recAnyR (\ _ -> extractR r)
               anyRcase = caseAnyR (extractR r) (\ _ -> extractR r)
            in rewrite $ \ c -> \case
                 BindCore bnd@(Rec _)       -> setFailMsg "anyR failed for Rec" $ inject <$> apply anyRrec c bnd
                 ExprCore e@(Case _ _ _ _)  -> setFailMsg "anyR failed for Case" $ inject <$> apply anyRcase c e
                 core                       -> apply (anyRdefault r) c core

  oneR :: RewriteH Core -> RewriteH Core
  oneR r = let oneRrec  = recOneR (\ _ -> extractR r)
               oneRcase = caseOneR (extractR r) (\ _ -> extractR r)
            in rewrite $ \ c -> \case
                 BindCore bnd@(Rec _)       -> setFailMsg "oneR failed for Rec" $ inject <$> apply oneRrec c bnd
                 ExprCore e@(Case _ _ _ _)  -> setFailMsg "oneR failed for Case" $ inject <$> apply oneRcase c e
                 core                       -> apply (oneRdefault r) c core

---------------------------------------------------------------------

-- | Translate a module.
--   Slightly different to the other congruence combinators: it passes in /all/ of the original to the reconstruction function.
modGutsT :: TranslateH CoreProg a -> (ModGuts -> a -> b) -> TranslateH ModGuts b
modGutsT t f = translate $ \ c modGuts -> f modGuts <$> apply t (c @@ 0) (bindsToProg (mg_binds modGuts))

-- | Rewrite the 'CoreProg' child of a module.
modGutsR :: RewriteH CoreProg -> RewriteH ModGuts
modGutsR r = modGutsT r (\ modguts p -> modguts {mg_binds = progToBinds p})

---------------------------------------------------------------------

-- | Translate an empty list.
progNilT :: b -> TranslateH CoreProg b
progNilT b = contextfreeT $ \case
                               ProgNil       -> pure b
                               ProgCons _ _  -> fail "not an empty program node."

progConsT' :: TranslateH CoreBind a1 -> TranslateH CoreProg a2 -> (HermitM a1 -> HermitM a2 -> HermitM b) -> TranslateH CoreProg b
progConsT' t1 t2 f = translate $ \ c -> \case
                                           ProgCons bd p -> f (apply t1 (c @@ 0) bd) (apply t2 (addBinding bd c @@ 1) p)
                                           _             -> fail "not a non-empty program node."

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

-- | Translate a binding group of the form: @NonRec@ 'Var' 'CoreExpr'
nonRecT :: TranslateH CoreExpr a -> (Var -> a -> b) -> TranslateH CoreBind b
nonRecT t f = translate $ \ c -> \case
                                    NonRec v e -> f v <$> apply t (c @@ 0) e
                                    _          -> fail "not a non-recursive binding-group node."

-- | Rewrite the 'CoreExpr' child of a binding group of the form: @NonRec@ 'Var' 'CoreExpr'
nonRecR :: RewriteH CoreExpr -> RewriteH CoreBind
nonRecR r = nonRecT r NonRec

recT' :: (Int -> TranslateH CoreDef a) -> ([HermitM a] -> HermitM b) -> TranslateH CoreBind b
recT' t f = translate $ \ c -> \case
         Rec bds -> -- Notice how we add the scoping bindings here *before* descending into each individual definition.
                    let c' = addBinding (Rec bds) c
                     in f [ apply (t n) (c' @@ n) (Def v e) -- here we convert from (Id,CoreExpr) to CoreDef
                          | ((v,e),n) <- zip bds [0..]
                          ]
         _       -> fail "not a recursive binding-group node."

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

-- | Translate a recursive definition of the form: @Def@ 'Id' 'CoreExpr'
defT :: TranslateH CoreExpr a -> (Id -> a -> b) -> TranslateH CoreDef b
defT t f = translate $ \ c (Def v e) -> f v <$> apply t (c @@ 0) e

-- | Rewrite the 'CoreExpr' child of a recursive definition of the form: @Def@ 'Id' 'CoreExpr'
defR :: RewriteH CoreExpr -> RewriteH CoreDef
defR r = defT r Def

---------------------------------------------------------------------

-- | Translate a case alternative of the form: ('AltCon', ['Id'], 'CoreExpr')
altT :: TranslateH CoreExpr a -> (AltCon -> [Id] -> a -> b) -> TranslateH CoreAlt b
altT t f = translate $ \ c (con,bs,e) -> f con bs <$> apply t (addAltBindings bs c @@ 0) e

-- | Rewrite the 'CoreExpr' child of a case alternative of the form: ('AltCon', 'Id', 'CoreExpr')
altR :: RewriteH CoreExpr -> RewriteH CoreAlt
altR r = altT r (,,)

---------------------------------------------------------------------

-- | Translate an expression of the form: @Var@ 'Var'
varT :: (Var -> b) -> TranslateH CoreExpr b
varT f = contextfreeT $ \case
                           Var v -> pure (f v)
                           _     -> fail "not a variable node."

-- | Translate an expression of the form: @Lit@ 'Literal'
litT :: (Literal -> b) -> TranslateH CoreExpr b
litT f = contextfreeT $ \case
                           Lit x -> pure (f x)
                           _     -> fail "not a literal node."


appT' :: TranslateH CoreExpr a1 -> TranslateH CoreExpr a2 -> (HermitM a1 -> HermitM a2 -> HermitM b) -> TranslateH CoreExpr b
appT' t1 t2 f = translate $ \ c -> \case
                                      App e1 e2 -> f (apply t1 (c @@ 0) e1) (apply t2 (c @@ 1) e2)
                                      _         -> fail "not an application node."

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

-- | Translate an expression of the form: @Lam@ 'Var' 'CoreExpr'
lamT :: TranslateH CoreExpr a -> (Var -> a -> b) -> TranslateH CoreExpr b
lamT t f = translate $ \ c -> \case
                                 Lam b e -> f b <$> apply t (addLambdaBinding b c @@ 0) e
                                 _       -> fail "not a lambda node."

-- | Rewrite the 'CoreExpr' child of an expression of the form: @Lam@ 'Var' 'CoreExpr'
lamR :: RewriteH CoreExpr -> RewriteH CoreExpr
lamR r = lamT r Lam


letT' :: TranslateH CoreBind a1 -> TranslateH CoreExpr a2 -> (HermitM a1 -> HermitM a2 -> HermitM b) -> TranslateH CoreExpr b
letT' t1 t2 f = translate $ \ c -> \case
        Let bds e -> f (apply t1 (c @@ 0) bds) (apply t2 (addBinding bds c @@ 1) e)
                -- use *original* env, because the bindings are self-binding,
                -- if they are recursive. See recT'.
        _         -> fail "not a let node."

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
         _                -> fail "not a case node."

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
                                  _           -> fail "not a cast node."

-- | Rewrite the 'CoreExpr' child of an expression of the form: @Cast@ 'CoreExpr' 'Coercion'
castR :: RewriteH CoreExpr -> RewriteH CoreExpr
castR r = castT r Cast

-- | Translate an expression of the form: @Tick@ 'CoreTickish' 'CoreExpr'
tickT :: TranslateH CoreExpr a -> (CoreTickish -> a -> b) -> TranslateH CoreExpr b
tickT t f = translate $ \ c -> \case
        Tick tk e -> f tk <$> apply t (c @@ 0) e
        _         -> fail "not a tick node."

-- | Rewrite the 'CoreExpr' child of an expression of the form: @Tick@ 'CoreTickish' 'CoreExpr'
tickR :: RewriteH CoreExpr -> RewriteH CoreExpr
tickR r = tickT r Tick

-- | Translate an expression of the form: @Type@ 'Type'
typeT :: (Type -> b) -> TranslateH CoreExpr b
typeT f = contextfreeT $ \case
                            Type t -> pure (f t)
                            _      -> fail "not a type node."

-- | Translate an expression of the form: @Coercion@ 'Coercion'
coercionT :: (Coercion -> b) -> TranslateH CoreExpr b
coercionT f = contextfreeT $ \case
                                Coercion co -> pure (f co)
                                _           -> fail "not a coercion node."

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


-- | Translate a program of the form: (@NonRec@ 'Var' 'CoreExpr') @:@ 'CoreProg'
consNonRecT :: TranslateH CoreExpr a1 -> TranslateH CoreProg a2 -> (Var -> a1 -> a2 -> b) -> TranslateH CoreProg b
consNonRecT t1 t2 f = progConsT (nonRecT t1 (,)) t2 (uncurry f)

-- | Rewrite all children of an expression of the form: (@NonRec@ 'Var' 'CoreExpr') @:@ 'CoreProg'
consNonRecAllR :: RewriteH CoreExpr -> RewriteH CoreProg -> RewriteH CoreProg
consNonRecAllR r1 r2 = progConsAllR (nonRecR r1) r2

-- | Rewrite any children of an expression of the form: (@NonRec@ 'Var' 'CoreExpr') @:@ 'CoreProg'
consNonRecAnyR :: RewriteH CoreExpr -> RewriteH CoreProg -> RewriteH CoreProg
consNonRecAnyR r1 r2 = progConsAnyR (nonRecR r1) r2

-- | Rewrite one child of an expression of the form: (@NonRec@ 'Var' 'CoreExpr') @:@ 'CoreProg'
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


-- | Translate an expression of the form: @Let@ (@NonRec@ 'Var' 'CoreExpr') 'CoreExpr'
letNonRecT :: TranslateH CoreExpr a1 -> TranslateH CoreExpr a2 -> (Var -> a1 -> a2 -> b) -> TranslateH CoreExpr b
letNonRecT t1 t2 f = letT (nonRecT t1 (,)) t2 (uncurry f)

-- | Rewrite all children of an expression of the form: @Let@ (@NonRec@ 'Var' 'CoreExpr') 'CoreExpr'
letNonRecAllR :: RewriteH CoreExpr -> RewriteH CoreExpr -> RewriteH CoreExpr
letNonRecAllR r1 r2 = letAllR (nonRecR r1) r2

-- | Rewrite any children of an expression of the form: @Let@ (@NonRec@ 'Var' 'CoreExpr') 'CoreExpr'
letNonRecAnyR :: RewriteH CoreExpr -> RewriteH CoreExpr -> RewriteH CoreExpr
letNonRecAnyR r1 r2 = letAnyR (nonRecR r1) r2

-- | Rewrite one child of an expression of the form: @Let@ (@NonRec@ 'Var' 'CoreExpr') 'CoreExpr'
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
