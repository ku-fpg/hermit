{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module HERMIT.Kure
    ( -- * KURE

      -- | All the required functionality of KURE is exported here, so other modules do not need to import KURE directly.
      module Language.KURE
    , module Language.KURE.BiTransform
    , module Language.KURE.Lens
    , module Language.KURE.ExtendableContext
    , module Language.KURE.Pathfinder
      -- * Sub-Modules
    , module HERMIT.Kure.Universes
      -- * Synonyms
    , TransformH
    , RewriteH
    , BiRewriteH
    , LensH
    , PathH
      -- * Utilities
    , inContextM

      -- * Congruence combinators
      -- ** Modguts
    , modGutsT, modGutsR
      -- ** Program
    , progNilT
    , progConsT, progConsAllR, progConsAnyR, progConsOneR
      -- ** Binding Groups
    , nonRecT, nonRecAllR, nonRecAnyR, nonRecOneR
    , recT, recAllR, recAnyR, recOneR
      -- ** Recursive Definitions
    , defT, defAllR, defAnyR, defOneR
      -- ** Case Alternatives
    , altT, altAllR, altAnyR, altOneR
      -- ** Expressions
    , varT, varR
    , litT, litR
    , appT, appAllR, appAnyR, appOneR
    , lamT, lamAllR, lamAnyR, lamOneR
    , letT, letAllR, letAnyR, letOneR
    , caseT, caseAllR, caseAnyR, caseOneR
    , castT, castAllR, castAnyR, castOneR
    , tickT, tickAllR, tickAnyR, tickOneR
    , typeT, typeR
    , coercionT, coercionR
      -- ** Composite Congruence Combinators
    , defOrNonRecT, defOrNonRecAllR, defOrNonRecAnyR, defOrNonRecOneR
    , recDefT, recDefAllR, recDefAnyR, recDefOneR
    , letNonRecT, letNonRecAllR, letNonRecAnyR, letNonRecOneR
    , letRecT, letRecAllR, letRecAnyR, letRecOneR
    , letRecDefT, letRecDefAllR, letRecDefAnyR, letRecDefOneR
    , consNonRecT, consNonRecAllR, consNonRecAnyR, consNonRecOneR
    , consRecT, consRecAllR, consRecAnyR, consRecOneR
    , consRecDefT, consRecDefAllR, consRecDefAnyR, consRecDefOneR
    , caseAltT, caseAltAllR, caseAltAnyR, caseAltOneR
      -- ** Recursive Composite Congruence Combinators
    , progBindsT, progBindsAllR, progBindsAnyR, progBindsOneR
      -- ** Types
    , tyVarT, tyVarR
    , litTyT, litTyR
    , appTyT, appTyAllR, appTyAnyR, appTyOneR
    , funTyT, funTyAllR, funTyAnyR, funTyOneR
    , forAllTyT, forAllTyAllR, forAllTyAnyR, forAllTyOneR
    , tyConAppT, tyConAppAllR, tyConAppAnyR, tyConAppOneR
      -- ** Coercions
    , reflT, reflR
    , tyConAppCoT, tyConAppCoAllR, tyConAppCoAnyR, tyConAppCoOneR
    , appCoT, appCoAllR, appCoAnyR, appCoOneR
    , forAllCoT, forAllCoAllR, forAllCoAnyR, forAllCoOneR
    , coVarCoT, coVarCoR
    , axiomInstCoT, axiomInstCoAllR, axiomInstCoAnyR, axiomInstCoOneR
    , symCoT, symCoR
    , transCoT, transCoAllR, transCoAnyR, transCoOneR
    , nthCoT, nthCoAllR, nthCoAnyR, nthCoOneR
    , instCoT, instCoAllR, instCoAnyR, instCoOneR
    , lrCoT, lrCoAllR, lrCoAnyR, lrCoOneR
    , subCoT, subCoR
    , univCoT, univCoAllR, univCoAnyR, univCoOneR
      -- ** Lemmas
    , conjT, conjAllR
    , disjT, disjAllR
    , implT, implAllR
    , equivT, equivAllR
    , forallT, forallR, forallsT, forallsR
      -- * Applicative
    , (<$>)
    , (<*>)
    ) where

import Control.Monad.Compat (ap, liftM)

import Language.KURE
import Language.KURE.BiTransform
import Language.KURE.Lens
import Language.KURE.ExtendableContext
import Language.KURE.Pathfinder

import HERMIT.Context
import HERMIT.Core
import HERMIT.GHC
import HERMIT.Kure.Universes
import HERMIT.Lemma
import HERMIT.Monad

import Prelude.Compat hiding ((<$>), (<*>))

---------------------------------------------------------------------

type TransformH a b = Transform HermitC HermitM a b
type RewriteH a     = Rewrite   HermitC HermitM a
type BiRewriteH a   = BiRewrite HermitC HermitM a
type LensH a b      = Lens      HermitC HermitM a b
type PathH          = Path Crumb

-- It is annoying that Applicative is not a superclass of Monad in 7.8.
-- This causes a warning which we ignore.
(<$>) :: Monad m => (a -> b) -> m a -> m b
(<$>) = liftM
{-# INLINE (<$>) #-}

(<*>) :: Monad m => m (a -> b) -> m a -> m b
(<*>) = ap
{-# INLINE (<*>) #-}

---------------------------------------------------------------------

-- | Walking over modules, programs, binding groups, definitions, expressions and case alternatives.
instance (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, HasEmptyContext c) => Walker c Core where

  allR :: forall m. MonadCatch m => Rewrite c m Core -> Rewrite c m Core
  allR r = prefixFailMsg "allR failed: " $
           rewrite $ \ c -> \case
             GutsCore guts  -> inject <$> applyT allRmodguts c guts
             ProgCore p     -> inject <$> applyT allRprog c p
             BindCore bn    -> inject <$> applyT allRbind c bn
             DefCore def    -> inject <$> applyT allRdef c def
             AltCore alt    -> inject <$> applyT allRalt c alt
             ExprCore e     -> inject <$> applyT allRexpr c e
    where
      allRmodguts :: MonadCatch m => Rewrite c m ModGuts
      allRmodguts = modGutsR (extractR r)
      {-# INLINE allRmodguts #-}

      allRprog :: MonadCatch m => Rewrite c m CoreProg
      allRprog = readerT $ \case
                              ProgCons{}  -> progConsAllR (extractR r) (extractR r)
                              _           -> idR
      {-# INLINE allRprog #-}

      allRbind :: MonadCatch m => Rewrite c m CoreBind
      allRbind = readerT $ \case
                              NonRec{}  -> nonRecAllR idR (extractR r) -- we don't descend into the Var
                              Rec _     -> recAllR (const $ extractR r)
      {-# INLINE allRbind #-}

      allRdef :: MonadCatch m => Rewrite c m CoreDef
      allRdef = defAllR idR (extractR r) -- we don't descend into the Id
      {-# INLINE allRdef #-}

      allRalt :: MonadCatch m => Rewrite c m CoreAlt
      allRalt = altAllR idR (const idR) (extractR r) -- we don't descend into the AltCon or Vars
      {-# INLINE allRalt #-}

      allRexpr :: MonadCatch m => Rewrite c m CoreExpr
      allRexpr = readerT $ \case
                              App{}   -> appAllR (extractR r) (extractR r)
                              Lam{}   -> lamAllR idR (extractR r) -- we don't descend into the Var
                              Let{}   -> letAllR (extractR r) (extractR r)
                              Case{}  -> caseAllR (extractR r) idR idR (const $ extractR r) -- we don't descend into the case binder or Type
                              Cast{}  -> castAllR (extractR r) idR -- we don't descend into the Coercion
                              Tick{}  -> tickAllR idR (extractR r) -- we don't descend into the Tickish
                              _       -> idR
      {-# INLINE allRexpr #-}

---------------------------------------------------------------------

-- | Walking over types (only).
instance (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c) => Walker c Type where

  allR :: MonadCatch m => Rewrite c m Type -> Rewrite c m Type
  allR r = prefixFailMsg "allR failed: " $
           readerT $ \case
                        AppTy{}     -> appTyAllR r r
                        FunTy{}     -> funTyAllR r r
                        ForAllTy{}  -> forAllTyAllR idR r
                        TyConApp{}  -> tyConAppAllR idR (const r)
                        _           -> idR

---------------------------------------------------------------------

-- | Walking over coercions (only).
instance (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c) => Walker c Coercion where

  allR :: MonadCatch m => Rewrite c m Coercion -> Rewrite c m Coercion
  allR r = prefixFailMsg "allR failed: " $
           readerT $ \case
                        TyConAppCo{}  -> tyConAppCoAllR idR (const r)
                        AppCo{}       -> appCoAllR r r
                        ForAllCo{}    -> forAllCoAllR idR r
                        SymCo{}       -> symCoR r
                        SubCo{}       -> subCoR r
                        TransCo{}     -> transCoAllR r r
                        NthCo{}       -> nthCoAllR idR r
                        InstCo{}      -> instCoAllR r idR
                        LRCo{}        -> lrCoAllR idR r
                        AxiomInstCo{} -> axiomInstCoAllR idR idR (const r)
                        _             -> idR

---------------------------------------------------------------------

-- | Walking over types and coercions.
instance (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c) => Walker c TyCo where

  allR :: forall m. MonadCatch m => Rewrite c m TyCo -> Rewrite c m TyCo
  allR r = prefixFailMsg "allR failed: " $
           rewrite $ \ c -> \case
             TypeCore ty     -> inject <$> applyT (allR $ extractR r) c ty -- exploiting the fact that types do not contain coercions
             CoercionCore co -> inject <$> applyT allRcoercion c co
    where
      allRcoercion :: MonadCatch m => Rewrite c m Coercion
      allRcoercion = readerT $ \case
                              Refl{}        -> reflR (extractR r)
                              TyConAppCo{}  -> tyConAppCoAllR idR (const $ extractR r) -- we don't descend into the TyCon
                              AppCo{}       -> appCoAllR (extractR r) (extractR r)
                              ForAllCo{}    -> forAllCoAllR idR (extractR r) -- we don't descend into the TyVar
                              SymCo{}       -> symCoR (extractR r)
                              SubCo{}       -> subCoR (extractR r)
                              TransCo{}     -> transCoAllR (extractR r) (extractR r)
                              InstCo{}      -> instCoAllR (extractR r) (extractR r)
                              NthCo{}       -> nthCoAllR idR (extractR r) -- we don't descend into the Int
                              LRCo{}        -> lrCoAllR idR (extractR r)
                              AxiomInstCo{} -> axiomInstCoAllR idR idR (const $ extractR r) -- we don't descend into the axiom or index
                              UnivCo{}      -> univCoAllR (extractR r) (extractR r) -- we don't descend into the provenance (FastString) or role
                              _             -> idR
      {-# INLINE allRcoercion #-}

---------------------------------------------------------------------

-- | Walking over modules, programs, binding groups, definitions, expressions, case alternatives, lemma quantifiers and lemma clauses.
instance (AddBindings c, ExtendPath c Crumb, HasEmptyContext c, LemmaContext c, ReadPath c Crumb) => Walker c LCore where

    allR :: forall m. MonadCatch m => Rewrite c m LCore -> Rewrite c m LCore
    allR r = prefixFailMsg "allR failed: " $
                rewrite $ \ c -> \case
                    LClause cl     -> inject <$> applyT allRclause c cl
                    LCore core     -> inject <$> applyT (allR $ extractR r) c core -- exploiting the fact that clause does not appear within Core
        where
            allRclause :: MonadCatch m => Rewrite c m Clause
            allRclause = readerT $ \case
                                Forall{} -> forallR idR (extractR r) -- we don't descend into the binders
                                Conj{}   -> conjAllR  (extractR r) (extractR r)
                                Disj{}   -> disjAllR  (extractR r) (extractR r)
                                Impl{}   -> implAllR  (extractR r) (extractR r)
                                Equiv{}  -> equivAllR (extractR r) (extractR r)
                                CTrue    -> return CTrue
            {-# INLINE allRclause #-}

---------------------------------------------------------------------

-- | Walking over modules, programs, binding groups, definitions, expressions, case alternatives, types, coercions, lemma quantifiers and lemma clauses.
instance (AddBindings c, ExtendPath c Crumb, HasEmptyContext c, LemmaContext c, ReadPath c Crumb) => Walker c LCoreTC where

    allR :: forall m. MonadCatch m => Rewrite c m LCoreTC -> Rewrite c m LCoreTC
    allR r = prefixFailMsg "allR failed: " $
                rewrite $ \ c -> \case
                    LTCCore (LClause cl)     -> inject <$> applyT allRclause c cl
                    LTCCore (LCore core)     -> inject <$> applyT (allR (extractR r :: Rewrite c m CoreTC)) c (Core core) -- convert to CoreTC, and exploit the fact that quantifiers and clauses will not appear in Core/CoreTC
                    LTCTyCo tyCo             -> inject <$> applyT (allR $ extractR r) c tyCo -- exploiting the fact that only types and coercions appear within types and coercions
        where
            allRclause :: MonadCatch m => Rewrite c m Clause
            allRclause = readerT $ \case
                                Forall{} -> forallR idR (extractR r) -- we don't descend into the binders
                                Conj{}   -> conjAllR (extractR r) (extractR r)
                                Disj{}   -> disjAllR (extractR r) (extractR r)
                                Impl{}   -> implAllR  (extractR r) (extractR r)
                                Equiv{}  -> equivAllR (extractR r) (extractR r)
                                CTrue    -> return CTrue
            {-# INLINE allRclause #-}

---------------------------------------------------------------------

-- | Walking over modules, programs, binding groups, definitions, expressions, case alternatives, types and coercions.
instance (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, HasEmptyContext c) => Walker c CoreTC where

  allR :: forall m. MonadCatch m => Rewrite c m CoreTC -> Rewrite c m CoreTC
  allR r = prefixFailMsg "allR failed: " $
           rewrite $ \ c -> \case
             Core (GutsCore guts)  -> inject <$> applyT allRmodguts c guts
             Core (ProgCore p)     -> inject <$> applyT allRprog c p
             Core (BindCore bn)    -> inject <$> applyT allRbind c bn
             Core (DefCore def)    -> inject <$> applyT allRdef c def
             Core (AltCore alt)    -> inject <$> applyT allRalt c alt
             Core (ExprCore e)     -> inject <$> applyT allRexpr c e
             TyCo tyCo             -> inject <$> applyT (allR $ extractR r) c tyCo -- exploiting the fact that only types and coercions appear within types and coercions
    where
      allRmodguts :: MonadCatch m => Rewrite c m ModGuts
      allRmodguts = modGutsR (extractR r)
      {-# INLINE allRmodguts #-}

      allRprog :: MonadCatch m => Rewrite c m CoreProg
      allRprog = readerT $ \case
                              ProgCons{}  -> progConsAllR (extractR r) (extractR r)
                              _           -> idR
      {-# INLINE allRprog #-}

      allRbind :: MonadCatch m => Rewrite c m CoreBind
      allRbind = readerT $ \case
                              NonRec{}  -> nonRecAllR idR (extractR r) -- we don't descend into the Var
                              Rec _     -> recAllR (const $ extractR r)
      {-# INLINE allRbind #-}

      allRdef :: MonadCatch m => Rewrite c m CoreDef
      allRdef = defAllR idR (extractR r) -- we don't descend into the Id
      {-# INLINE allRdef #-}

      allRalt :: MonadCatch m => Rewrite c m CoreAlt
      allRalt = altAllR idR (const idR) (extractR r) -- we don't descend into the AltCon or Vars
      {-# INLINE allRalt #-}

      allRexpr :: MonadCatch m => Rewrite c m CoreExpr
      allRexpr = readerT $ \case
                              App{}      -> appAllR (extractR r) (extractR r)
                              Lam{}      -> lamAllR idR (extractR r) -- we don't descend into the Var
                              Let{}      -> letAllR (extractR r) (extractR r)
                              Case{}     -> caseAllR (extractR r) idR (extractR r) (const $ extractR r) -- we don't descend into the case binder
                              Cast{}     -> castAllR (extractR r) (extractR r)
                              Tick{}     -> tickAllR idR (extractR r) -- we don't descend into the Tickish
                              Type{}     -> typeR (extractR r)
                              Coercion{} -> coercionR (extractR r)
                              _          -> idR
      {-# INLINE allRexpr #-}

---------------------------------------------------------------------

-- Note that we deliberately set the context to empty when descending into a ModGuts.
-- This is to hide the top-level definitions that we include in the context when focusses on ModGuts.
-- This is slightly awkward, but pragmatically useful.

-- | Transform a module.
--   Slightly different to the other congruence combinators: it passes in /all/ of the original to the reconstruction function.
modGutsT :: (ExtendPath c Crumb, HasEmptyContext c, Monad m) => Transform c m CoreProg a -> (ModGuts -> a -> b) -> Transform c m ModGuts b
modGutsT t f = transform $ \ c guts -> f guts <$> applyT t (setEmptyContext c @@ ModGuts_Prog) (bindsToProg $ mg_binds guts)
{-# INLINE modGutsT #-}

-- | Rewrite the 'CoreProg' child of a module.
modGutsR :: (ExtendPath c Crumb, HasEmptyContext c, Monad m) => Rewrite c m CoreProg -> Rewrite c m ModGuts
modGutsR r = modGutsT r (\ guts p -> guts {mg_binds = progToBinds p})
{-# INLINE modGutsR #-}

---------------------------------------------------------------------

-- | Transform an empty list.
progNilT :: Monad m => b -> Transform c m CoreProg b
progNilT b = contextfreeT $ \case
                               ProgNil       -> return b
                               ProgCons _ _  -> fail "not an empty program."
{-# INLINE progNilT #-}

-- | Transform a program of the form: ('CoreBind' @:@ 'CoreProg')
progConsT :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, Monad m) => Transform c m CoreBind a1 -> Transform c m CoreProg a2 -> (a1 -> a2 -> b) -> Transform c m CoreProg b
progConsT t1 t2 f = transform $ \ c -> \case
                                          ProgCons bd p -> f <$> applyT t1 (c @@ ProgCons_Head) bd <*> applyT t2 (addBindingGroup bd c @@ ProgCons_Tail) p
                                          _             -> fail "not a non-empty program."
{-# INLINE progConsT #-}

-- | Rewrite all children of a program of the form: ('CoreBind' @:@ 'CoreProg')
progConsAllR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, Monad m) => Rewrite c m CoreBind -> Rewrite c m CoreProg -> Rewrite c m CoreProg
progConsAllR r1 r2 = progConsT r1 r2 ProgCons
{-# INLINE progConsAllR #-}

-- | Rewrite any children of a program of the form: ('CoreBind' @:@ 'CoreProg')
progConsAnyR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, MonadCatch m) => Rewrite c m CoreBind -> Rewrite c m CoreProg -> Rewrite c m CoreProg
progConsAnyR r1 r2 = unwrapAnyR $ progConsAllR (wrapAnyR r1) (wrapAnyR r2)
{-# INLINE progConsAnyR #-}

-- | Rewrite one child of a program of the form: ('CoreBind' @:@ 'CoreProg')
progConsOneR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, MonadCatch m) => Rewrite c m CoreBind -> Rewrite c m CoreProg -> Rewrite c m CoreProg
progConsOneR r1 r2 = unwrapOneR $  progConsAllR (wrapOneR r1) (wrapOneR r2)
{-# INLINE progConsOneR #-}

---------------------------------------------------------------------

-- | Transform a binding group of the form: @NonRec@ 'Var' 'CoreExpr'
nonRecT :: (ExtendPath c Crumb, Monad m) => Transform c m Var a1 -> Transform c m CoreExpr a2 -> (a1 -> a2 -> b) -> Transform c m CoreBind b
nonRecT t1 t2 f = transform $ \ c -> \case
                                        NonRec v e -> f <$> applyT t1 (c @@ NonRec_Var) v <*> applyT t2 (c @@ NonRec_RHS) e
                                        _          -> fail "not a non-recursive binding group."
{-# INLINE nonRecT #-}

-- | Rewrite all children of a binding group of the form: @NonRec@ 'Var' 'CoreExpr'
nonRecAllR :: (ExtendPath c Crumb, Monad m) => Rewrite c m Var -> Rewrite c m CoreExpr -> Rewrite c m CoreBind
nonRecAllR r1 r2 = nonRecT r1 r2 NonRec
{-# INLINE nonRecAllR #-}

-- | Rewrite any children of a binding group of the form: @NonRec@ 'Var' 'CoreExpr'
nonRecAnyR :: (ExtendPath c Crumb, MonadCatch m) => Rewrite c m Var -> Rewrite c m CoreExpr -> Rewrite c m CoreBind
nonRecAnyR r1 r2 = unwrapAnyR (nonRecAllR (wrapAnyR r1) (wrapAnyR r2))
{-# INLINE nonRecAnyR #-}

-- | Rewrite one child of a binding group of the form: @NonRec@ 'Var' 'CoreExpr'
nonRecOneR :: (ExtendPath c Crumb, MonadCatch m) => Rewrite c m Var -> Rewrite c m CoreExpr -> Rewrite c m CoreBind
nonRecOneR r1 r2 = unwrapOneR (nonRecAllR (wrapOneR r1) (wrapOneR r2))
{-# INLINE nonRecOneR #-}


-- | Transform a binding group of the form: @Rec@ ['CoreDef']
recT :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, Monad m) => (Int -> Transform c m CoreDef a) -> ([a] -> b) -> Transform c m CoreBind b
recT t f = transform $ \ c -> \case
         Rec bds -> -- The group is recursive, so we add all other bindings in the group to the context (excluding the one under consideration).
                    f <$> sequence [ applyT (t n) (addDefBindingsExcept n bds c @@ Rec_Def n) (Def i e) -- here we convert from (Id,CoreExpr) to CoreDef
                                   | ((i,e),n) <- zip bds [0..]
                                   ]
         _       -> fail "not a recursive binding group."
{-# INLINE recT #-}

-- | Rewrite all children of a binding group of the form: @Rec@ ['CoreDef']
recAllR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, Monad m) => (Int -> Rewrite c m CoreDef) -> Rewrite c m CoreBind
recAllR rs = recT rs defsToRecBind
{-# INLINE recAllR #-}

-- | Rewrite any children of a binding group of the form: @Rec@ ['CoreDef']
recAnyR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, MonadCatch m) => (Int -> Rewrite c m CoreDef) -> Rewrite c m CoreBind
recAnyR rs = unwrapAnyR $ recAllR (wrapAnyR . rs)
{-# INLINE recAnyR #-}

-- | Rewrite one child of a binding group of the form: @Rec@ ['CoreDef']
recOneR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, MonadCatch m) => (Int -> Rewrite c m CoreDef) -> Rewrite c m CoreBind
recOneR rs = unwrapOneR $ recAllR (wrapOneR . rs)
{-# INLINE recOneR #-}

---------------------------------------------------------------------

-- | Transform a recursive definition of the form: @Def@ 'Id' 'CoreExpr'
defT :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, Monad m) => Transform c m Id a1 -> Transform c m CoreExpr a2 -> (a1 -> a2 -> b) -> Transform c m CoreDef b
defT t1 t2 f = transform $ \ c (Def i e) -> f <$> applyT t1 (c @@ Def_Id) i <*> applyT t2 (addDefBinding i c @@ Def_RHS) e
{-# INLINE defT #-}

-- | Rewrite all children of a recursive definition of the form: @Def@ 'Id' 'CoreExpr'
defAllR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, Monad m) => Rewrite c m Id -> Rewrite c m CoreExpr -> Rewrite c m CoreDef
defAllR r1 r2 = defT r1 r2 Def
{-# INLINE defAllR #-}

-- | Rewrite any children of a recursive definition of the form: @Def@ 'Id' 'CoreExpr'
defAnyR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, MonadCatch m) => Rewrite c m Id -> Rewrite c m CoreExpr -> Rewrite c m CoreDef
defAnyR r1 r2 = unwrapAnyR (defAllR (wrapAnyR r1) (wrapAnyR r2))
{-# INLINE defAnyR #-}

-- | Rewrite one child of a recursive definition of the form: @Def@ 'Id' 'CoreExpr'
defOneR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, MonadCatch m) => Rewrite c m Id -> Rewrite c m CoreExpr -> Rewrite c m CoreDef
defOneR r1 r2 = unwrapOneR (defAllR (wrapOneR r1) (wrapOneR r2))
{-# INLINE defOneR #-}

---------------------------------------------------------------------

-- | Transform a case alternative of the form: ('AltCon', ['Var'], 'CoreExpr')
altT :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, Monad m) => Transform c m AltCon a1 -> (Int -> Transform c m Var a2) -> Transform c m CoreExpr a3 -> (a1 -> [a2] -> a3 -> b) -> Transform c m CoreAlt b
altT t1 ts t2 f = transform $ \ c (con,vs,e) -> f <$> applyT t1 (c @@ Alt_Con) con
                                                  <*> sequence [ applyT (ts n) (c @@ Alt_Var n) v | (v,n) <- zip vs [1..] ]
                                                  <*> applyT t2 (addAltBindings vs c @@ Alt_RHS) e
{-# INLINE altT #-}

-- | Rewrite all children of a case alternative of the form: ('AltCon', 'Id', 'CoreExpr')
altAllR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, Monad m) => Rewrite c m AltCon -> (Int -> Rewrite c m Var) -> Rewrite c m CoreExpr -> Rewrite c m CoreAlt
altAllR r1 rs r2 = altT r1 rs r2 (,,)
{-# INLINE altAllR #-}

-- | Rewrite any children of a case alternative of the form: ('AltCon', 'Id', 'CoreExpr')
altAnyR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, MonadCatch m) => Rewrite c m AltCon -> (Int -> Rewrite c m Var) -> Rewrite c m CoreExpr -> Rewrite c m CoreAlt
altAnyR r1 rs r2 = unwrapAnyR (altAllR (wrapAnyR r1) (wrapAnyR . rs) (wrapAnyR r2))
{-# INLINE altAnyR #-}

-- | Rewrite one child of a case alternative of the form: ('AltCon', 'Id', 'CoreExpr')
altOneR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, MonadCatch m) => Rewrite c m AltCon -> (Int -> Rewrite c m Var) -> Rewrite c m CoreExpr -> Rewrite c m CoreAlt
altOneR r1 rs r2 = unwrapOneR (altAllR (wrapOneR r1) (wrapOneR . rs) (wrapOneR r2))
{-# INLINE altOneR #-}

---------------------------------------------------------------------

-- | Transform an expression of the form: @Var@ 'Id'
varT :: (ExtendPath c Crumb, Monad m) => Transform c m Id b -> Transform c m CoreExpr b
varT t = transform $ \ c -> \case
                               Var v -> applyT t (c @@ Var_Id) v
                               _     -> fail "not a variable."
{-# INLINE varT #-}

-- | Rewrite the 'Id' child in an expression of the form: @Var@ 'Id'
varR :: (ExtendPath c Crumb, Monad m) => Rewrite c m Id -> Rewrite c m CoreExpr
varR r = varT (Var <$> r)
{-# INLINE varR #-}


-- | Transform an expression of the form: @Lit@ 'Literal'
litT :: (ExtendPath c Crumb, Monad m) => Transform c m Literal b -> Transform c m CoreExpr b
litT t = transform $ \ c -> \case
                               Lit x -> applyT t (c @@ Lit_Lit) x
                               _     -> fail "not a literal."
{-# INLINE litT #-}

-- | Rewrite the 'Literal' child in an expression of the form: @Lit@ 'Literal'
litR :: (ExtendPath c Crumb, Monad m) => Rewrite c m Literal -> Rewrite c m CoreExpr
litR r = litT (Lit <$> r)
{-# INLINE litR #-}


-- | Transform an expression of the form: @App@ 'CoreExpr' 'CoreExpr'
appT :: (ExtendPath c Crumb, Monad m) => Transform c m CoreExpr a1 -> Transform c m CoreExpr a2 -> (a1 -> a2 -> b) -> Transform c m CoreExpr b
appT t1 t2 f = transform $ \ c -> \case
                                     App e1 e2 -> f <$> applyT t1 (c @@ App_Fun) e1 <*> applyT t2 (c @@ App_Arg) e2
                                     _         -> fail "not an application."
{-# INLINE appT #-}

-- | Rewrite all children of an expression of the form: @App@ 'CoreExpr' 'CoreExpr'
appAllR :: (ExtendPath c Crumb, Monad m) => Rewrite c m CoreExpr -> Rewrite c m CoreExpr -> Rewrite c m CoreExpr
appAllR r1 r2 = appT r1 r2 App
{-# INLINE appAllR #-}

-- | Rewrite any children of an expression of the form: @App@ 'CoreExpr' 'CoreExpr'
appAnyR :: (ExtendPath c Crumb, MonadCatch m) => Rewrite c m CoreExpr -> Rewrite c m CoreExpr -> Rewrite c m CoreExpr
appAnyR r1 r2 = unwrapAnyR $ appAllR (wrapAnyR r1) (wrapAnyR r2)
{-# INLINE appAnyR #-}

-- | Rewrite one child of an expression of the form: @App@ 'CoreExpr' 'CoreExpr'
appOneR :: (ExtendPath c Crumb, MonadCatch m) => Rewrite c m CoreExpr -> Rewrite c m CoreExpr -> Rewrite c m CoreExpr
appOneR r1 r2 = unwrapOneR $ appAllR (wrapOneR r1) (wrapOneR r2)
{-# INLINE appOneR #-}


-- | Transform an expression of the form: @Lam@ 'Var' 'CoreExpr'
lamT :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, Monad m) => Transform c m Var a1 -> Transform c m CoreExpr a2 -> (a1 -> a2 -> b) -> Transform c m CoreExpr b
lamT t1 t2 f = transform $ \ c -> \case
                                     Lam v e -> f <$> applyT t1 (c @@ Lam_Var) v <*> applyT t2 (addLambdaBinding v c @@ Lam_Body) e
                                     _       -> fail "not a lambda."
{-# INLINE lamT #-}

-- | Rewrite all children of an expression of the form: @Lam@ 'Var' 'CoreExpr'
lamAllR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, Monad m) => Rewrite c m Var -> Rewrite c m CoreExpr -> Rewrite c m CoreExpr
lamAllR r1 r2 = lamT r1 r2 Lam
{-# INLINE lamAllR #-}

-- | Rewrite any children of an expression of the form: @Lam@ 'Var' 'CoreExpr'
lamAnyR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, MonadCatch m) => Rewrite c m Var -> Rewrite c m CoreExpr -> Rewrite c m CoreExpr
lamAnyR r1 r2 = unwrapAnyR $ lamAllR (wrapAnyR r1) (wrapAnyR r2)
{-# INLINE lamAnyR #-}

-- | Rewrite one child of an expression of the form: @Lam@ 'Var' 'CoreExpr'
lamOneR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, MonadCatch m) => Rewrite c m Var -> Rewrite c m CoreExpr -> Rewrite c m CoreExpr
lamOneR r1 r2 = unwrapOneR $ lamAllR (wrapOneR r1) (wrapOneR r2)
{-# INLINE lamOneR #-}


-- | Transform an expression of the form: @Let@ 'CoreBind' 'CoreExpr'
letT :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, Monad m) => Transform c m CoreBind a1 -> Transform c m CoreExpr a2 -> (a1 -> a2 -> b) -> Transform c m CoreExpr b
letT t1 t2 f = transform $ \ c -> \case
        Let bds e -> -- Note we use the *original* context for the binding group.
                     -- If the bindings are recursive, they will be added to the context by recT.
                     f <$> applyT t1 (c @@ Let_Bind) bds <*> applyT t2 (addBindingGroup bds c @@ Let_Body) e
        _         -> fail "not a let node."
{-# INLINE letT #-}

-- | Rewrite all children of an expression of the form: @Let@ 'CoreBind' 'CoreExpr'
letAllR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, Monad m) => Rewrite c m CoreBind -> Rewrite c m CoreExpr -> Rewrite c m CoreExpr
letAllR r1 r2 = letT r1 r2 Let
{-# INLINE letAllR #-}

-- | Rewrite any children of an expression of the form: @Let@ 'CoreBind' 'CoreExpr'
letAnyR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, MonadCatch m) => Rewrite c m CoreBind -> Rewrite c m CoreExpr -> Rewrite c m CoreExpr
letAnyR r1 r2 = unwrapAnyR $ letAllR (wrapAnyR r1) (wrapAnyR r2)
{-# INLINE letAnyR #-}

-- | Rewrite one child of an expression of the form: @Let@ 'CoreBind' 'CoreExpr'
letOneR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, MonadCatch m) => Rewrite c m CoreBind -> Rewrite c m CoreExpr -> Rewrite c m CoreExpr
letOneR r1 r2 = unwrapOneR $ letAllR (wrapOneR r1) (wrapOneR r2)
{-# INLINE letOneR #-}


-- | Transform an expression of the form: @Case@ 'CoreExpr' 'Id' 'Type' ['CoreAlt']
caseT :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, Monad m)
      => Transform c m CoreExpr e
      -> Transform c m Id w
      -> Transform c m Type ty
      -> (Int -> Transform c m CoreAlt alt)
      -> (e -> w -> ty -> [alt] -> b)
      -> Transform c m CoreExpr b
caseT te tw tty talts f = transform $ \ c -> \case
         Case e w ty alts -> f <$> applyT te (c @@ Case_Scrutinee) e
                               <*> applyT tw (c @@ Case_Binder) w
                               <*> applyT tty (c @@ Case_Type) ty
                               <*> sequence [ applyT (talts n) (addCaseBinderBinding (w,e,alt) c @@ Case_Alt n) alt
                                            | (alt,n) <- zip alts [0..]
                                            ]
         _                -> fail "not a case."
{-# INLINE caseT #-}

-- | Rewrite all children of an expression of the form: @Case@ 'CoreExpr' 'Id' 'Type' ['CoreAlt']
caseAllR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, Monad m)
         => Rewrite c m CoreExpr
         -> Rewrite c m Id
         -> Rewrite c m Type
         -> (Int -> Rewrite c m CoreAlt)
         -> Rewrite c m CoreExpr
caseAllR re rw rty ralts = caseT re rw rty ralts Case
{-# INLINE caseAllR #-}

-- | Rewrite any children of an expression of the form: @Case@ 'CoreExpr' 'Id' 'Type' ['CoreAlt']
caseAnyR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, MonadCatch m)
         => Rewrite c m CoreExpr
         -> Rewrite c m Id
         -> Rewrite c m Type
         -> (Int -> Rewrite c m CoreAlt)
         -> Rewrite c m CoreExpr
caseAnyR re rw rty ralts = unwrapAnyR $ caseAllR (wrapAnyR re) (wrapAnyR rw) (wrapAnyR rty) (wrapAnyR . ralts)
{-# INLINE caseAnyR #-}

-- | Rewrite one child of an expression of the form: @Case@ 'CoreExpr' 'Id' 'Type' ['CoreAlt']
caseOneR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, MonadCatch m)
         => Rewrite c m CoreExpr
         -> Rewrite c m Id
         -> Rewrite c m Type
         -> (Int -> Rewrite c m CoreAlt)
         -> Rewrite c m CoreExpr
caseOneR re rw rty ralts = unwrapOneR $ caseAllR (wrapOneR re) (wrapOneR rw) (wrapOneR rty) (wrapOneR . ralts)
{-# INLINE caseOneR #-}


-- | Transform an expression of the form: @Cast@ 'CoreExpr' 'Coercion'
castT :: (ExtendPath c Crumb, Monad m) => Transform c m CoreExpr a1 -> Transform c m Coercion a2 -> (a1 -> a2 -> b) -> Transform c m CoreExpr b
castT t1 t2 f = transform $ \ c -> \case
                                      Cast e co -> f <$> applyT t1 (c @@ Cast_Expr) e <*> applyT t2 (c @@ Cast_Co) co
                                      _         -> fail "not a cast."
{-# INLINE castT #-}

-- | Rewrite all children of an expression of the form: @Cast@ 'CoreExpr' 'Coercion'
castAllR :: (ExtendPath c Crumb, Monad m) => Rewrite c m CoreExpr -> Rewrite c m Coercion -> Rewrite c m CoreExpr
castAllR r1 r2 = castT r1 r2 Cast
{-# INLINE castAllR #-}

-- | Rewrite any children of an expression of the form: @Cast@ 'CoreExpr' 'Coercion'
castAnyR :: (ExtendPath c Crumb, MonadCatch m) => Rewrite c m CoreExpr -> Rewrite c m Coercion -> Rewrite c m CoreExpr
castAnyR r1 r2 = unwrapAnyR $ castAllR (wrapAnyR r1) (wrapAnyR r2)
{-# INLINE castAnyR #-}

-- | Rewrite one child of an expression of the form: @Cast@ 'CoreExpr' 'Coercion'
castOneR :: (ExtendPath c Crumb, MonadCatch m) => Rewrite c m CoreExpr -> Rewrite c m Coercion -> Rewrite c m CoreExpr
castOneR r1 r2 = unwrapOneR $ castAllR (wrapOneR r1) (wrapOneR r2)
{-# INLINE castOneR #-}


-- | Transform an expression of the form: @Tick@ 'CoreTickish' 'CoreExpr'
tickT :: (ExtendPath c Crumb, Monad m) => Transform c m CoreTickish a1 -> Transform c m CoreExpr a2 -> (a1 -> a2 -> b) -> Transform c m CoreExpr b
tickT t1 t2 f = transform $ \ c -> \case
                                      Tick tk e -> f <$> applyT t1 (c @@ Tick_Tick) tk <*> applyT t2 (c @@ Tick_Expr) e
                                      _         -> fail "not a tick."
{-# INLINE tickT #-}

-- | Rewrite all children of an expression of the form: @Tick@ 'CoreTickish' 'CoreExpr'
tickAllR :: (ExtendPath c Crumb, Monad m) => Rewrite c m CoreTickish -> Rewrite c m CoreExpr -> Rewrite c m CoreExpr
tickAllR r1 r2 = tickT r1 r2 Tick
{-# INLINE tickAllR #-}

-- | Rewrite any children of an expression of the form: @Tick@ 'CoreTickish' 'CoreExpr'
tickAnyR :: (ExtendPath c Crumb, MonadCatch m) => Rewrite c m CoreTickish -> Rewrite c m CoreExpr -> Rewrite c m CoreExpr
tickAnyR r1 r2 = unwrapAnyR $ tickAllR (wrapAnyR r1) (wrapAnyR r2)
{-# INLINE tickAnyR #-}

-- | Rewrite any children of an expression of the form: @Tick@ 'CoreTickish' 'CoreExpr'
tickOneR :: (ExtendPath c Crumb, MonadCatch m) => Rewrite c m CoreTickish -> Rewrite c m CoreExpr -> Rewrite c m CoreExpr
tickOneR r1 r2 = unwrapOneR $ tickAllR (wrapOneR r1) (wrapOneR r2)
{-# INLINE tickOneR #-}


-- | Transform an expression of the form: @Type@ 'Type'
typeT :: (ExtendPath c Crumb, Monad m) => Transform c m Type b -> Transform c m CoreExpr b
typeT t = transform $ \ c -> \case
                                Type ty -> applyT t (c @@ Type_Type) ty
                                _       -> fail "not a type."
{-# INLINE typeT #-}

-- | Rewrite the 'Type' child in an expression of the form: @Type@ 'Type'
typeR :: (ExtendPath c Crumb, Monad m) => Rewrite c m Type -> Rewrite c m CoreExpr
typeR r = typeT (Type <$> r)
{-# INLINE typeR #-}


-- | Transform an expression of the form: @Coercion@ 'Coercion'
coercionT :: (ExtendPath c Crumb, Monad m) => Transform c m Coercion b -> Transform c m CoreExpr b
coercionT t = transform $ \ c -> \case
                                    Coercion co -> applyT t (c @@ Co_Co) co
                                    _           -> fail "not a coercion."
{-# INLINE coercionT #-}

-- | Rewrite the 'Coercion' child in an expression of the form: @Coercion@ 'Coercion'
coercionR :: (ExtendPath c Crumb, Monad m) => Rewrite c m Coercion -> Rewrite c m CoreExpr
coercionR r = coercionT (Coercion <$> r)
{-# INLINE coercionR #-}

---------------------------------------------------------------------

-- Some composite congruence combinators to export.

-- | Transform a definition of the form @NonRec 'Var' 'CoreExpr'@ or @Def 'Id' 'CoreExpr'@
defOrNonRecT :: (Injection CoreBind g, Injection CoreDef g, ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, MonadCatch m) => Transform c m Var a1 -> Transform c m CoreExpr a2 -> (a1 -> a2 -> b) -> Transform c m g b
defOrNonRecT t1 t2 f = promoteBindT (nonRecT t1 t2 f)
                    <+ promoteDefT  (defT    t1 t2 f)
{-# INLINE defOrNonRecT #-}

-- | Rewrite all children of a definition of the form @NonRec 'Var' 'CoreExpr'@ or @Def 'Id' 'CoreExpr'@
defOrNonRecAllR :: (Injection CoreBind g, Injection CoreDef g, ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, MonadCatch m) => Rewrite c m Var -> Rewrite c m CoreExpr -> Rewrite c m g
defOrNonRecAllR r1 r2 = promoteBindR (nonRecAllR r1 r2)
                     <+ promoteDefR  (defAllR    r1 r2)
{-# INLINE defOrNonRecAllR #-}

-- | Rewrite any children of a definition of the form @NonRec 'Var' 'CoreExpr'@ or @Def 'Id' 'CoreExpr'@
defOrNonRecAnyR :: (Injection CoreBind g, Injection CoreDef g, ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, MonadCatch m) => Rewrite c m Var -> Rewrite c m CoreExpr -> Rewrite c m g
defOrNonRecAnyR r1 r2 = unwrapAnyR $ defOrNonRecAllR (wrapAnyR r1) (wrapAnyR r2)
{-# INLINE defOrNonRecAnyR #-}

-- | Rewrite one child of a definition of the form @NonRec 'Var' 'CoreExpr'@ or @Def 'Id' 'CoreExpr'@
defOrNonRecOneR :: (Injection CoreBind g, Injection CoreDef g, ExtendPath c Crumb, AddBindings c, MonadCatch m) => Rewrite c m Var -> Rewrite c m CoreExpr -> Rewrite c m g
defOrNonRecOneR r1 r2 = unwrapAnyR $ defOrNonRecOneR (wrapAnyR r1) (wrapAnyR r2)
{-# INLINE defOrNonRecOneR #-}


-- | Transform a binding group of the form: @Rec@ [('Id', 'CoreExpr')]
recDefT :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, Monad m) => (Int -> (Transform c m Id a1, Transform c m CoreExpr a2)) -> ([(a1,a2)] -> b) -> Transform c m CoreBind b
recDefT ts = recT (\ n -> uncurry defT (ts n) (,))
{-# INLINE recDefT #-}

-- | Rewrite all children of a binding group of the form: @Rec@ [('Id', 'CoreExpr')]
recDefAllR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, Monad m) => (Int -> (Rewrite c m Id, Rewrite c m CoreExpr)) -> Rewrite c m CoreBind
recDefAllR rs = recAllR (\ n -> uncurry defAllR (rs n))
{-# INLINE recDefAllR #-}

-- | Rewrite any children of a binding group of the form: @Rec@ [('Id', 'CoreExpr')]
recDefAnyR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, MonadCatch m) => (Int -> (Rewrite c m Id, Rewrite c m CoreExpr)) -> Rewrite c m CoreBind
recDefAnyR rs = recAnyR (\ n -> uncurry defAnyR (rs n))
{-# INLINE recDefAnyR #-}

-- | Rewrite one child of a binding group of the form: @Rec@ [('Id', 'CoreExpr')]
recDefOneR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, MonadCatch m) => (Int -> (Rewrite c m Id, Rewrite c m CoreExpr)) -> Rewrite c m CoreBind
recDefOneR rs = recOneR (\ n -> uncurry defOneR (rs n))
{-# INLINE recDefOneR #-}


-- | Transform a program of the form: (@NonRec@ 'Var' 'CoreExpr') @:@ 'CoreProg'
consNonRecT :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, Monad m) => Transform c m Var a1 -> Transform c m CoreExpr a2 -> Transform c m CoreProg a3 -> (a1 -> a2 -> a3 -> b) -> Transform c m CoreProg b
consNonRecT t1 t2 t3 f = progConsT (nonRecT t1 t2 (,)) t3 (uncurry f)
{-# INLINE consNonRecT #-}

-- | Rewrite all children of an expression of the form: (@NonRec@ 'Var' 'CoreExpr') @:@ 'CoreProg'
consNonRecAllR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, Monad m) => Rewrite c m Var -> Rewrite c m CoreExpr -> Rewrite c m CoreProg -> Rewrite c m CoreProg
consNonRecAllR r1 r2 r3 = progConsAllR (nonRecAllR r1 r2) r3
{-# INLINE consNonRecAllR #-}

-- | Rewrite any children of an expression of the form: (@NonRec@ 'Var' 'CoreExpr') @:@ 'CoreProg'
consNonRecAnyR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, MonadCatch m) => Rewrite c m Var -> Rewrite c m CoreExpr -> Rewrite c m CoreProg -> Rewrite c m CoreProg
consNonRecAnyR r1 r2 r3 = progConsAllR (nonRecAnyR r1 r2) r3
{-# INLINE consNonRecAnyR #-}

-- | Rewrite one child of an expression of the form: (@NonRec@ 'Var' 'CoreExpr') @:@ 'CoreProg'
consNonRecOneR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, MonadCatch m) => Rewrite c m Var -> Rewrite c m CoreExpr -> Rewrite c m CoreProg -> Rewrite c m CoreProg
consNonRecOneR r1 r2 r3 = progConsAllR (nonRecOneR r1 r2) r3
{-# INLINE consNonRecOneR #-}


-- | Transform an expression of the form: (@Rec@ ['CoreDef']) @:@ 'CoreProg'
consRecT :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, Monad m) => (Int -> Transform c m CoreDef a1) -> Transform c m CoreProg a2 -> ([a1] -> a2 -> b) -> Transform c m CoreProg b
consRecT ts t = progConsT (recT ts id) t
{-# INLINE consRecT #-}

-- | Rewrite all children of an expression of the form: (@Rec@ ['CoreDef']) @:@ 'CoreProg'
consRecAllR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, Monad m) => (Int -> Rewrite c m CoreDef) -> Rewrite c m CoreProg -> Rewrite c m CoreProg
consRecAllR rs r = progConsAllR (recAllR rs) r
{-# INLINE consRecAllR #-}

-- | Rewrite any children of an expression of the form: (@Rec@ ['CoreDef']) @:@ 'CoreProg'
consRecAnyR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, MonadCatch m) => (Int -> Rewrite c m CoreDef) -> Rewrite c m CoreProg -> Rewrite c m CoreProg
consRecAnyR rs r = progConsAnyR (recAnyR rs) r
{-# INLINE consRecAnyR #-}

-- | Rewrite one child of an expression of the form: (@Rec@ ['CoreDef']) @:@ 'CoreProg'
consRecOneR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, MonadCatch m) => (Int -> Rewrite c m CoreDef) -> Rewrite c m CoreProg -> Rewrite c m CoreProg
consRecOneR rs r = progConsOneR (recOneR rs) r
{-# INLINE consRecOneR #-}


-- | Transform an expression of the form: (@Rec@ [('Id', 'CoreExpr')]) @:@ 'CoreProg'
consRecDefT :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, Monad m) => (Int -> (Transform c m Id a1, Transform c m CoreExpr a2)) -> Transform c m CoreProg a3 -> ([(a1,a2)] -> a3 -> b) -> Transform c m CoreProg b
consRecDefT ts t = consRecT (\ n -> uncurry defT (ts n) (,)) t
{-# INLINE consRecDefT #-}

-- | Rewrite all children of an expression of the form: (@Rec@ [('Id', 'CoreExpr')]) @:@ 'CoreProg'
consRecDefAllR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, Monad m) => (Int -> (Rewrite c m Id, Rewrite c m CoreExpr)) -> Rewrite c m CoreProg -> Rewrite c m CoreProg
consRecDefAllR rs r = consRecAllR (\ n -> uncurry defAllR (rs n)) r
{-# INLINE consRecDefAllR #-}

-- | Rewrite any children of an expression of the form: (@Rec@ [('Id', 'CoreExpr')]) @:@ 'CoreProg'
consRecDefAnyR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, MonadCatch m) => (Int -> (Rewrite c m Id, Rewrite c m CoreExpr)) -> Rewrite c m CoreProg -> Rewrite c m CoreProg
consRecDefAnyR rs r = consRecAnyR (\ n -> uncurry defAnyR (rs n)) r
{-# INLINE consRecDefAnyR #-}

-- | Rewrite one child of an expression of the form: (@Rec@ [('Id', 'CoreExpr')]) @:@ 'CoreProg'
consRecDefOneR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, MonadCatch m) => (Int -> (Rewrite c m Id, Rewrite c m CoreExpr)) -> Rewrite c m CoreProg -> Rewrite c m CoreProg
consRecDefOneR rs r = consRecOneR (\ n -> uncurry defOneR (rs n)) r
{-# INLINE consRecDefOneR #-}


-- | Transform an expression of the form: @Let@ (@NonRec@ 'Var' 'CoreExpr') 'CoreExpr'
letNonRecT :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, Monad m) => Transform c m Var a1 -> Transform c m CoreExpr a2 -> Transform c m CoreExpr a3 -> (a1 -> a2 -> a3 -> b) -> Transform c m CoreExpr b
letNonRecT t1 t2 t3 f = letT (nonRecT t1 t2 (,)) t3 (uncurry f)
{-# INLINE letNonRecT #-}

-- | Rewrite all children of an expression of the form: @Let@ (@NonRec@ 'Var' 'CoreExpr') 'CoreExpr'
letNonRecAllR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, Monad m) => Rewrite c m Var -> Rewrite c m CoreExpr -> Rewrite c m CoreExpr -> Rewrite c m CoreExpr
letNonRecAllR r1 r2 r3 = letAllR (nonRecAllR r1 r2) r3
{-# INLINE letNonRecAllR #-}

-- | Rewrite any children of an expression of the form: @Let@ (@NonRec@ 'Var' 'CoreExpr') 'CoreExpr'
letNonRecAnyR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, MonadCatch m) => Rewrite c m Var -> Rewrite c m CoreExpr -> Rewrite c m CoreExpr -> Rewrite c m CoreExpr
letNonRecAnyR r1 r2 r3 = letAnyR (nonRecAnyR r1 r2) r3
{-# INLINE letNonRecAnyR #-}

-- | Rewrite one child of an expression of the form: @Let@ (@NonRec@ 'Var' 'CoreExpr') 'CoreExpr'
letNonRecOneR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, MonadCatch m) => Rewrite c m Var -> Rewrite c m CoreExpr -> Rewrite c m CoreExpr -> Rewrite c m CoreExpr
letNonRecOneR r1 r2 r3 = letOneR (nonRecOneR r1 r2) r3
{-# INLINE letNonRecOneR #-}


-- | Transform an expression of the form: @Let@ (@Rec@ ['CoreDef']) 'CoreExpr'
letRecT :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, Monad m) => (Int -> Transform c m CoreDef a1) -> Transform c m CoreExpr a2 -> ([a1] -> a2 -> b) -> Transform c m CoreExpr b
letRecT ts t = letT (recT ts id) t
{-# INLINE letRecT #-}

-- | Rewrite all children of an expression of the form: @Let@ (@Rec@ ['CoreDef']) 'CoreExpr'
letRecAllR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, Monad m) => (Int -> Rewrite c m CoreDef) -> Rewrite c m CoreExpr -> Rewrite c m CoreExpr
letRecAllR rs r = letAllR (recAllR rs) r
{-# INLINE letRecAllR #-}

-- | Rewrite any children of an expression of the form: @Let@ (@Rec@ ['CoreDef']) 'CoreExpr'
letRecAnyR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, MonadCatch m) => (Int -> Rewrite c m CoreDef) -> Rewrite c m CoreExpr -> Rewrite c m CoreExpr
letRecAnyR rs r = letAnyR (recAnyR rs) r
{-# INLINE letRecAnyR #-}

-- | Rewrite one child of an expression of the form: @Let@ (@Rec@ ['CoreDef']) 'CoreExpr'
letRecOneR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, MonadCatch m) => (Int -> Rewrite c m CoreDef) -> Rewrite c m CoreExpr -> Rewrite c m CoreExpr
letRecOneR rs r = letOneR (recOneR rs) r
{-# INLINE letRecOneR #-}


-- | Transform an expression of the form: @Let@ (@Rec@ [('Id', 'CoreExpr')]) 'CoreExpr'
letRecDefT :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, Monad m) => (Int -> (Transform c m Id a1, Transform c m CoreExpr a2)) -> Transform c m CoreExpr a3 -> ([(a1,a2)] -> a3 -> b) -> Transform c m CoreExpr b
letRecDefT ts t = letRecT (\ n -> uncurry defT (ts n) (,)) t
{-# INLINE letRecDefT #-}

-- | Rewrite all children of an expression of the form: @Let@ (@Rec@ [('Id', 'CoreExpr')]) 'CoreExpr'
letRecDefAllR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, Monad m) => (Int -> (Rewrite c m Id, Rewrite c m CoreExpr)) -> Rewrite c m CoreExpr -> Rewrite c m CoreExpr
letRecDefAllR rs r = letRecAllR (\ n -> uncurry defAllR (rs n)) r
{-# INLINE letRecDefAllR #-}

-- | Rewrite any children of an expression of the form: @Let@ (@Rec@ [('Id', 'CoreExpr')]) 'CoreExpr'
letRecDefAnyR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, MonadCatch m) => (Int -> (Rewrite c m Id, Rewrite c m CoreExpr)) -> Rewrite c m CoreExpr -> Rewrite c m CoreExpr
letRecDefAnyR rs r = letRecAnyR (\ n -> uncurry defAnyR (rs n)) r
{-# INLINE letRecDefAnyR #-}

-- | Rewrite one child of an expression of the form: @Let@ (@Rec@ [('Id', 'CoreExpr')]) 'CoreExpr'
letRecDefOneR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, MonadCatch m) => (Int -> (Rewrite c m Id, Rewrite c m CoreExpr)) -> Rewrite c m CoreExpr -> Rewrite c m CoreExpr
letRecDefOneR rs r = letRecOneR (\ n -> uncurry defOneR (rs n)) r
{-# INLINE letRecDefOneR #-}


-- | Transform an expression of the form: @Case@ 'CoreExpr' 'Id' 'Type' [('AltCon', ['Var'], 'CoreExpr')]
caseAltT :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, Monad m)
         => Transform c m CoreExpr sc
         -> Transform c m Id w
         -> Transform c m Type ty
         -> (Int -> (Transform c m AltCon con, (Int -> Transform c m Var v), Transform c m CoreExpr rhs)) -> (sc -> w -> ty -> [(con,[v],rhs)] -> b)
         -> Transform c m CoreExpr b
caseAltT tsc tw tty talts = caseT tsc tw tty (\ n -> let (tcon,tvs,te) = talts n in altT tcon tvs te (,,))
{-# INLINE caseAltT #-}

-- | Rewrite all children of an expression of the form: @Case@ 'CoreExpr' 'Id' 'Type' [('AltCon', ['Var'], 'CoreExpr')]
caseAltAllR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, Monad m)
            => Rewrite c m CoreExpr
            -> Rewrite c m Id
            -> Rewrite c m Type
            -> (Int -> (Rewrite c m AltCon, (Int -> Rewrite c m Var), Rewrite c m CoreExpr))
            -> Rewrite c m CoreExpr
caseAltAllR rsc rw rty ralts = caseAllR rsc rw rty (\ n -> let (rcon,rvs,re) = ralts n in altAllR rcon rvs re)
{-# INLINE caseAltAllR #-}

-- | Rewrite any children of an expression of the form: @Case@ 'CoreExpr' 'Id' 'Type' [('AltCon', ['Var'], 'CoreExpr')]
caseAltAnyR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, MonadCatch m)
            => Rewrite c m CoreExpr
            -> Rewrite c m Id
            -> Rewrite c m Type
            -> (Int -> (Rewrite c m AltCon, (Int -> Rewrite c m Var), Rewrite c m CoreExpr))
            -> Rewrite c m CoreExpr
caseAltAnyR rsc rw rty ralts = caseAnyR rsc rw rty (\ n -> let (rcon,rvs,re) = ralts n in altAnyR rcon rvs re)
{-# INLINE caseAltAnyR #-}

-- | Rewrite one child of an expression of the form: @Case@ 'CoreExpr' 'Id' 'Type' [('AltCon', ['Var'], 'CoreExpr')]
caseAltOneR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, MonadCatch m)
            => Rewrite c m CoreExpr
            -> Rewrite c m Id
            -> Rewrite c m Type
            -> (Int -> (Rewrite c m AltCon, (Int -> Rewrite c m Var), Rewrite c m CoreExpr))
            -> Rewrite c m CoreExpr
caseAltOneR rsc rw rty ralts = caseOneR rsc rw rty (\ n -> let (rcon,rvs,re) = ralts n in altOneR rcon rvs re)
{-# INLINE caseAltOneR #-}

---------------------------------------------------------------------

-- Recursive composite congruence combinators.

-- | Transform all top-level binding groups in a program.
progBindsT :: forall c m a b. (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, MonadCatch m) => (Int -> Transform c m CoreBind a) -> ([a] -> b) -> Transform c m CoreProg b
progBindsT ts f = f <$> progBindsTaux 0
  where
    progBindsTaux :: Int -> Transform c m CoreProg [a]
    progBindsTaux n = progNilT [] <+ progConsT (ts n) (progBindsTaux (succ n)) (:)
{-# INLINE progBindsT #-}

-- | Rewrite all top-level binding groups in a program.
progBindsAllR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, MonadCatch m) => (Int -> Rewrite c m CoreBind) -> Rewrite c m CoreProg
progBindsAllR rs = progBindsT rs bindsToProg
{-# INLINE progBindsAllR #-}

-- | Rewrite any top-level binding groups in a program.
progBindsAnyR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, MonadCatch m) => (Int -> Rewrite c m CoreBind) -> Rewrite c m CoreProg
progBindsAnyR rs = unwrapAnyR $ progBindsAllR (wrapAnyR . rs)
{-# INLINE progBindsAnyR #-}

-- | Rewrite any top-level binding groups in a program.
progBindsOneR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, MonadCatch m) => (Int -> Rewrite c m CoreBind) -> Rewrite c m CoreProg
progBindsOneR rs = unwrapOneR $ progBindsAllR (wrapOneR . rs)
{-# INLINE progBindsOneR #-}

---------------------------------------------------------------------
---------------------------------------------------------------------

-- Types

-- | Transform a type of the form: @TyVarTy@ 'TyVar'
tyVarT :: (ExtendPath c Crumb, Monad m) => Transform c m TyVar b -> Transform c m Type b
tyVarT t = transform $ \ c -> \case
                                 TyVarTy v -> applyT t (c @@ TyVarTy_TyVar) v
                                 _         -> fail "not a type variable."
{-# INLINE tyVarT #-}

-- | Rewrite the 'TyVar' child of a type of the form: @TyVarTy@ 'TyVar'
tyVarR :: (ExtendPath c Crumb, Monad m) => Rewrite c m TyVar -> Rewrite c m Type
tyVarR r = tyVarT (TyVarTy <$> r)
{-# INLINE tyVarR #-}


-- | Transform a type of the form: @LitTy@ 'TyLit'
litTyT :: (ExtendPath c Crumb, Monad m) => Transform c m TyLit b -> Transform c m Type b
litTyT t = transform $ \ c -> \case
                                 LitTy x -> applyT t (c @@ LitTy_TyLit) x
                                 _       -> fail "not a type literal."
{-# INLINE litTyT #-}

-- | Rewrite the 'TyLit' child of a type of the form: @LitTy@ 'TyLit'
litTyR :: (ExtendPath c Crumb, Monad m) => Rewrite c m TyLit -> Rewrite c m Type
litTyR r = litTyT (LitTy <$> r)
{-# INLINE litTyR #-}


-- | Transform a type of the form: @AppTy@ 'Type' 'Type'
appTyT :: (ExtendPath c Crumb, Monad m) => Transform c m Type a1 -> Transform c m Type a2 -> (a1 -> a2 -> b) -> Transform c m Type b
appTyT t1 t2 f = transform $ \ c -> \case
                                     AppTy ty1 ty2 -> f <$> applyT t1 (c @@ AppTy_Fun) ty1 <*> applyT t2 (c @@ AppTy_Arg) ty2
                                     _             -> fail "not a type application."
{-# INLINE appTyT #-}

-- | Rewrite all children of a type of the form: @AppTy@ 'Type' 'Type'
appTyAllR :: (ExtendPath c Crumb, Monad m) => Rewrite c m Type -> Rewrite c m Type -> Rewrite c m Type
appTyAllR r1 r2 = appTyT r1 r2 AppTy
{-# INLINE appTyAllR #-}

-- | Rewrite any children of a type of the form: @AppTy@ 'Type' 'Type'
appTyAnyR :: (ExtendPath c Crumb, MonadCatch m) => Rewrite c m Type -> Rewrite c m Type -> Rewrite c m Type
appTyAnyR r1 r2 = unwrapAnyR $ appTyAllR (wrapAnyR r1) (wrapAnyR r2)
{-# INLINE appTyAnyR #-}

-- | Rewrite one child of a type of the form: @AppTy@ 'Type' 'Type'
appTyOneR :: (ExtendPath c Crumb, MonadCatch m) => Rewrite c m Type -> Rewrite c m Type -> Rewrite c m Type
appTyOneR r1 r2 = unwrapOneR $ appTyAllR (wrapOneR r1) (wrapOneR r2)
{-# INLINE appTyOneR #-}


-- | Transform a type of the form: @FunTy@ 'Type' 'Type'
funTyT :: (ExtendPath c Crumb, Monad m) => Transform c m Type a1 -> Transform c m Type a2 -> (a1 -> a2 -> b) -> Transform c m Type b
funTyT t1 t2 f = transform $ \ c -> \case
                                     FunTy ty1 ty2 -> f <$> applyT t1 (c @@ FunTy_Dom) ty1 <*> applyT t2 (c @@ FunTy_CoDom) ty2
                                     _             -> fail "not a function type."
{-# INLINE funTyT #-}

-- | Rewrite all children of a type of the form: @FunTy@ 'Type' 'Type'
funTyAllR :: (ExtendPath c Crumb, Monad m) => Rewrite c m Type -> Rewrite c m Type -> Rewrite c m Type
funTyAllR r1 r2 = funTyT r1 r2 FunTy
{-# INLINE funTyAllR #-}

-- | Rewrite any children of a type of the form: @FunTy@ 'Type' 'Type'
funTyAnyR :: (ExtendPath c Crumb, MonadCatch m) => Rewrite c m Type -> Rewrite c m Type -> Rewrite c m Type
funTyAnyR r1 r2 = unwrapAnyR $ funTyAllR (wrapAnyR r1) (wrapAnyR r2)
{-# INLINE funTyAnyR #-}

-- | Rewrite one child of a type of the form: @FunTy@ 'Type' 'Type'
funTyOneR :: (ExtendPath c Crumb, MonadCatch m) => Rewrite c m Type -> Rewrite c m Type -> Rewrite c m Type
funTyOneR r1 r2 = unwrapOneR $ funTyAllR (wrapOneR r1) (wrapOneR r2)
{-# INLINE funTyOneR #-}


-- | Transform a type of the form: @ForAllTy@ 'Var' 'Type'
forAllTyT :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, Monad m) => Transform c m Var a1 -> Transform c m Type a2 -> (a1 -> a2 -> b) -> Transform c m Type b
forAllTyT t1 t2 f = transform $ \ c -> \case
                                          ForAllTy v ty -> f <$> applyT t1 (c @@ ForAllTy_Var) v <*> applyT t2 (addForallBinding v c @@ ForAllTy_Body) ty
                                          _             -> fail "not a forall type."
{-# INLINE forAllTyT #-}

-- | Rewrite all children of a type of the form: @ForAllTy@ 'Var' 'Type'
forAllTyAllR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, Monad m) => Rewrite c m Var -> Rewrite c m Type -> Rewrite c m Type
forAllTyAllR r1 r2 = forAllTyT r1 r2 ForAllTy
{-# INLINE forAllTyAllR #-}

-- | Rewrite any children of a type of the form: @ForAllTy@ 'Var' 'Type'
forAllTyAnyR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, MonadCatch m) => Rewrite c m Var -> Rewrite c m Type -> Rewrite c m Type
forAllTyAnyR r1 r2 = unwrapAnyR $ forAllTyAllR (wrapAnyR r1) (wrapAnyR r2)
{-# INLINE forAllTyAnyR #-}

-- | Rewrite one child of a type of the form: @ForAllTy@ 'Var' 'Type'
forAllTyOneR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, MonadCatch m) => Rewrite c m Var -> Rewrite c m Type -> Rewrite c m Type
forAllTyOneR r1 r2 = unwrapOneR $ forAllTyAllR (wrapOneR r1) (wrapOneR r2)
{-# INLINE forAllTyOneR #-}


-- | Transform a type of the form: @TyConApp@ 'TyCon' ['KindOrType']
tyConAppT :: (ExtendPath c Crumb, Monad m) => Transform c m TyCon a1 -> (Int -> Transform c m KindOrType a2) -> (a1 -> [a2] -> b) -> Transform c m Type b
tyConAppT t ts f = transform $ \ c -> \case
                                         TyConApp con tys -> f <$> applyT t (c @@ TyConApp_TyCon) con <*> sequence [ applyT (ts n) (c @@ TyConApp_Arg n) ty | (ty,n) <- zip tys [0..] ]
                                         _                -> fail "not a type-constructor application."
{-# INLINE tyConAppT #-}

-- | Rewrite all children of a type of the form: @TyConApp@ 'TyCon' ['KindOrType']
tyConAppAllR :: (ExtendPath c Crumb, Monad m) => Rewrite c m TyCon -> (Int -> Rewrite c m KindOrType) -> Rewrite c m Type
tyConAppAllR r rs = tyConAppT r rs TyConApp
{-# INLINE tyConAppAllR #-}

-- | Rewrite any children of a type of the form: @TyConApp@ 'TyCon' ['KindOrType']
tyConAppAnyR :: (ExtendPath c Crumb, MonadCatch m) => Rewrite c m TyCon -> (Int -> Rewrite c m KindOrType) -> Rewrite c m Type
tyConAppAnyR r rs = unwrapAnyR $ tyConAppAllR (wrapAnyR r) (wrapAnyR . rs)
{-# INLINE tyConAppAnyR #-}

-- | Rewrite one child of a type of the form: @TyConApp@ 'TyCon' ['KindOrType']
tyConAppOneR :: (ExtendPath c Crumb, MonadCatch m) => Rewrite c m TyCon -> (Int -> Rewrite c m KindOrType) -> Rewrite c m Type
tyConAppOneR r rs = unwrapOneR $ tyConAppAllR (wrapOneR r) (wrapOneR . rs)
{-# INLINE tyConAppOneR #-}

---------------------------------------------------------------------
---------------------------------------------------------------------

-- Coercions
-- TODO: review and bring all these up-to-date for Coercions w/ Roles in 7.8

-- | Transform a coercion of the form: @Refl@ 'Role' 'Type'
reflT :: (ExtendPath c Crumb, Monad m) => Transform c m Type a1 -> (Role -> a1 -> b) -> Transform c m Coercion b
reflT t f = transform $ \ c -> \case
                                 Refl r ty -> f r <$> applyT t (c @@ Refl_Type) ty
                                 _         -> fail "not a reflexive coercion."

-- | Rewrite the 'Type' child of a coercion of the form: @Refl@ 'Role' 'Type'
reflR :: (ExtendPath c Crumb, Monad m) => Rewrite c m Type -> Rewrite c m Coercion
reflR r = reflT r Refl
{-# INLINE reflT #-}
{-# INLINE reflR #-}

-- | Transform a coercion of the form: @TyConAppCo@ 'Role' 'TyCon' ['Coercion']
tyConAppCoT :: (ExtendPath c Crumb, Monad m) => Transform c m TyCon a1 -> (Int -> Transform c m Coercion a2) -> (Role -> a1 -> [a2] -> b) -> Transform c m Coercion b
tyConAppCoT t ts f = transform $ \ c -> \case
                                           TyConAppCo r con coes -> f r <$> applyT t (c @@ TyConAppCo_TyCon) con <*> sequence [ applyT (ts n) (c @@ TyConAppCo_Arg n) co | (co,n) <- zip coes [0..] ]
                                           _                     -> fail "not a type-constructor coercion."
{-# INLINE tyConAppCoT #-}

-- | Rewrite all children of a coercion of the form: @TyConAppCo@ 'TyCon' ['Coercion']
tyConAppCoAllR :: (ExtendPath c Crumb, Monad m) => Rewrite c m TyCon -> (Int -> Rewrite c m Coercion) -> Rewrite c m Coercion
tyConAppCoAllR r rs = tyConAppCoT r rs TyConAppCo
{-# INLINE tyConAppCoAllR #-}

-- | Rewrite any children of a coercion of the form: @TyConAppCo@ 'TyCon' ['Coercion']
tyConAppCoAnyR :: (ExtendPath c Crumb, MonadCatch m) => Rewrite c m TyCon -> (Int -> Rewrite c m Coercion) -> Rewrite c m Coercion
tyConAppCoAnyR r rs = unwrapAnyR $ tyConAppCoAllR (wrapAnyR r) (wrapAnyR . rs)
{-# INLINE tyConAppCoAnyR #-}

-- | Rewrite one child of a coercion of the form: @TyConAppCo@ 'TyCon' ['Coercion']
tyConAppCoOneR :: (ExtendPath c Crumb, MonadCatch m) => Rewrite c m TyCon -> (Int -> Rewrite c m Coercion) -> Rewrite c m Coercion
tyConAppCoOneR r rs = unwrapOneR $ tyConAppCoAllR (wrapOneR r) (wrapOneR . rs)
{-# INLINE tyConAppCoOneR #-}


-- | Transform a coercion of the form: @AppCo@ 'Coercion' 'Coercion'
appCoT :: (ExtendPath c Crumb, Monad m) => Transform c m Coercion a1 -> Transform c m Coercion a2 -> (a1 -> a2 -> b) -> Transform c m Coercion b
appCoT t1 t2 f = transform $ \ c -> \case
                                     AppCo co1 co2 -> f <$> applyT t1 (c @@ AppCo_Fun) co1 <*> applyT t2 (c @@ AppCo_Arg) co2
                                     _             -> fail "not a coercion application."
{-# INLINE appCoT #-}

-- | Rewrite all children of a coercion of the form: @AppCo@ 'Coercion' 'Coercion'
appCoAllR :: (ExtendPath c Crumb, Monad m) => Rewrite c m Coercion -> Rewrite c m Coercion -> Rewrite c m Coercion
appCoAllR r1 r2 = appCoT r1 r2 AppCo
{-# INLINE appCoAllR #-}

-- | Rewrite any children of a coercion of the form: @AppCo@ 'Coercion' 'Coercion'
appCoAnyR :: (ExtendPath c Crumb, MonadCatch m) => Rewrite c m Coercion -> Rewrite c m Coercion -> Rewrite c m Coercion
appCoAnyR r1 r2 = unwrapAnyR $ appCoAllR (wrapAnyR r1) (wrapAnyR r2)
{-# INLINE appCoAnyR #-}

-- | Rewrite one child of a coercion of the form: @AppCo@ 'Coercion' 'Coercion'
appCoOneR :: (ExtendPath c Crumb, MonadCatch m) => Rewrite c m Coercion -> Rewrite c m Coercion -> Rewrite c m Coercion
appCoOneR r1 r2 = unwrapOneR $ appCoAllR (wrapOneR r1) (wrapOneR r2)
{-# INLINE appCoOneR #-}


-- | Transform a coercion of the form: @ForAllCo@ 'TyVar' 'Coercion'
forAllCoT :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, Monad m) => Transform c m TyVar a1 -> Transform c m Coercion a2 -> (a1 -> a2 -> b) -> Transform c m Coercion b
forAllCoT t1 t2 f = transform $ \ c -> \case
                                          ForAllCo v co -> f <$> applyT t1 (c @@ ForAllCo_TyVar) v <*> applyT t2 (addForallBinding v c @@ ForAllCo_Body) co
                                          _             -> fail "not a forall coercion."
{-# INLINE forAllCoT #-}

-- | Rewrite all children of a coercion of the form: @ForAllCo@ 'TyVar' 'Coercion'
forAllCoAllR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, Monad m) => Rewrite c m TyVar -> Rewrite c m Coercion -> Rewrite c m Coercion
forAllCoAllR r1 r2 = forAllCoT r1 r2 ForAllCo
{-# INLINE forAllCoAllR #-}

-- | Rewrite any children of a coercion of the form: @ForAllCo@ 'TyVar' 'Coercion'
forAllCoAnyR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, MonadCatch m) => Rewrite c m TyVar -> Rewrite c m Coercion -> Rewrite c m Coercion
forAllCoAnyR r1 r2 = unwrapAnyR $ forAllCoAllR (wrapAnyR r1) (wrapAnyR r2)
{-# INLINE forAllCoAnyR #-}

-- | Rewrite one child of a coercion of the form: @ForAllCo@ 'TyVar' 'Coercion'
forAllCoOneR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, MonadCatch m) => Rewrite c m TyVar -> Rewrite c m Coercion -> Rewrite c m Coercion
forAllCoOneR r1 r2 = unwrapOneR $ forAllCoAllR (wrapOneR r1) (wrapOneR r2)
{-# INLINE forAllCoOneR #-}


-- | Transform a coercion of the form: @CoVarCo@ 'CoVar'
coVarCoT :: (ExtendPath c Crumb, Monad m) => Transform c m CoVar b -> Transform c m Coercion b
coVarCoT t = transform $ \ c -> \case
                                   CoVarCo v -> applyT t (c @@ CoVarCo_CoVar) v
                                   _         -> fail "not a coercion variable."
{-# INLINE coVarCoT #-}

-- | Rewrite the 'CoVar' child of a coercion of the form: @CoVarCo@ 'CoVar'
coVarCoR :: (ExtendPath c Crumb, Monad m) => Rewrite c m CoVar -> Rewrite c m Coercion
coVarCoR r = coVarCoT (CoVarCo <$> r)
{-# INLINE coVarCoR #-}

-- | Transform a coercion of the form: @AxiomInstCo@ ('CoAxiom' 'Branched') 'BranchIndex' ['Coercion']
axiomInstCoT :: (ExtendPath c Crumb, Monad m) => Transform c m (CoAxiom Branched) a1 -> Transform c m BranchIndex a2 -> (Int -> Transform c m Coercion a3) -> (a1 -> a2 -> [a3] -> b) -> Transform c m Coercion b
axiomInstCoT t1 t2 ts f = transform $ \ c -> \case
                                                AxiomInstCo ax idx coes -> f <$> applyT t1 (c @@ AxiomInstCo_Axiom) ax <*> applyT t2 (c @@ AxiomInstCo_Index) idx <*> sequence [ applyT (ts n) (c @@ AxiomInstCo_Arg n) co | (co,n) <- zip coes [0..] ]
                                                _                       -> fail "not a coercion axiom instantiation."
{-# INLINE axiomInstCoT #-}

-- | Rewrite all children of a coercion of the form: @AxiomInstCo@ ('CoAxiom' 'Branched') 'BranchIndex' ['Coercion']
axiomInstCoAllR :: (ExtendPath c Crumb, Monad m) => Rewrite c m (CoAxiom Branched) -> Rewrite c m BranchIndex -> (Int -> Rewrite c m Coercion) -> Rewrite c m Coercion
axiomInstCoAllR r1 r2 rs = axiomInstCoT r1 r2 rs AxiomInstCo
{-# INLINE axiomInstCoAllR #-}

-- | Rewrite any children of a coercion of the form: @AxiomInstCo@ ('CoAxiom' 'Branched') 'BranchIndex' ['Coercion']
axiomInstCoAnyR :: (ExtendPath c Crumb, MonadCatch m) => Rewrite c m (CoAxiom Branched) -> Rewrite c m BranchIndex -> (Int -> Rewrite c m Coercion) -> Rewrite c m Coercion
axiomInstCoAnyR r1 r2 rs = unwrapAnyR $ axiomInstCoAllR (wrapAnyR r1) (wrapAnyR r2) (wrapAnyR . rs)
{-# INLINE axiomInstCoAnyR #-}

-- | Rewrite one child of a coercion of the form: @AxiomInstCo@ ('CoAxiom' 'Branched') 'BranchIndex' ['Coercion']
axiomInstCoOneR :: (ExtendPath c Crumb, MonadCatch m) => Rewrite c m (CoAxiom Branched) -> Rewrite c m BranchIndex -> (Int -> Rewrite c m Coercion) -> Rewrite c m Coercion
axiomInstCoOneR r1 r2 rs = unwrapOneR $ axiomInstCoAllR (wrapOneR r1) (wrapOneR r2) (wrapOneR . rs)
{-# INLINE axiomInstCoOneR #-}


-- | Transform a coercion of the form: @SymCo@ 'Coercion'
symCoT :: (ExtendPath c Crumb, Monad m) => Transform c m Coercion b -> Transform c m Coercion b
symCoT t = transform $ \ c -> \case
                                   SymCo co -> applyT t (c @@ SymCo_Co) co
                                   _        -> fail "not a symmetric coercion."
{-# INLINE symCoT #-}

-- | Rewrite the 'Coercion' child of a coercion of the form: @SymCo@ 'Coercion'
symCoR :: (ExtendPath c Crumb, Monad m) => Rewrite c m Coercion -> Rewrite c m Coercion
symCoR r = symCoT (SymCo <$> r)
{-# INLINE symCoR #-}


-- | Transform a coercion of the form: @TransCo@ 'Coercion' 'Coercion'
transCoT :: (ExtendPath c Crumb, Monad m) => Transform c m Coercion a1 -> Transform c m Coercion a2 -> (a1 -> a2 -> b) -> Transform c m Coercion b
transCoT t1 t2 f = transform $ \ c -> \case
                                          TransCo co1 co2 -> f <$> applyT t1 (c @@ TransCo_Left) co1 <*> applyT t2 (c @@ TransCo_Right) co2
                                          _               -> fail "not a transitive coercion."
{-# INLINE transCoT #-}

-- | Rewrite all children of a coercion of the form: @TransCo@ 'Coercion' 'Coercion'
transCoAllR :: (ExtendPath c Crumb, Monad m) => Rewrite c m Coercion -> Rewrite c m Coercion -> Rewrite c m Coercion
transCoAllR r1 r2 = transCoT r1 r2 TransCo
{-# INLINE transCoAllR #-}

-- | Rewrite any children of a coercion of the form: @TransCo@ 'Coercion' 'Coercion'
transCoAnyR :: (ExtendPath c Crumb, MonadCatch m) => Rewrite c m Coercion -> Rewrite c m Coercion -> Rewrite c m Coercion
transCoAnyR r1 r2 = unwrapAnyR $ transCoAllR (wrapAnyR r1) (wrapAnyR r2)
{-# INLINE transCoAnyR #-}

-- | Rewrite one child of a coercion of the form: @TransCo@ 'Coercion' 'Coercion'
transCoOneR :: (ExtendPath c Crumb, MonadCatch m) => Rewrite c m Coercion -> Rewrite c m Coercion -> Rewrite c m Coercion
transCoOneR r1 r2 = unwrapOneR $ transCoAllR (wrapOneR r1) (wrapOneR r2)
{-# INLINE transCoOneR #-}


-- | Transform a coercion of the form: @NthCo@ 'Int' 'Coercion'
nthCoT :: (ExtendPath c Crumb, Monad m) => Transform c m Int a1 -> Transform c m Coercion a2 -> (a1 -> a2 -> b) -> Transform c m Coercion b
nthCoT t1 t2 f = transform $ \ c -> \case
                                          NthCo n co -> f <$> applyT t1 (c @@ NthCo_Int) n <*> applyT t2 (c @@ NthCo_Co) co
                                          _          -> fail "not an Nth coercion."
{-# INLINE nthCoT #-}

-- | Rewrite all children of a coercion of the form: @NthCo@ 'Int' 'Coercion'
nthCoAllR :: (ExtendPath c Crumb, Monad m) => Rewrite c m Int -> Rewrite c m Coercion -> Rewrite c m Coercion
nthCoAllR r1 r2 = nthCoT r1 r2 NthCo
{-# INLINE nthCoAllR #-}

-- | Rewrite any children of a coercion of the form: @NthCo@ 'Int' 'Coercion'
nthCoAnyR :: (ExtendPath c Crumb, MonadCatch m) => Rewrite c m Int -> Rewrite c m Coercion -> Rewrite c m Coercion
nthCoAnyR r1 r2 = unwrapAnyR $ nthCoAllR (wrapAnyR r1) (wrapAnyR r2)
{-# INLINE nthCoAnyR #-}

-- | Rewrite one child of a coercion of the form: @NthCo@ 'Int' 'Coercion'
nthCoOneR :: (ExtendPath c Crumb, MonadCatch m) => Rewrite c m Int -> Rewrite c m Coercion -> Rewrite c m Coercion
nthCoOneR r1 r2 = unwrapOneR $ nthCoAllR (wrapOneR r1) (wrapOneR r2)
{-# INLINE nthCoOneR #-}


-- | Transform a coercion of the form: @LRCo@ 'LeftOrRight' 'Coercion'
lrCoT :: (ExtendPath c Crumb, Monad m) => Transform c m LeftOrRight a1 -> Transform c m Coercion a2 -> (a1 -> a2 -> b) -> Transform c m Coercion b
lrCoT t1 t2 f = transform $ \ c -> \case
                                      LRCo lr co -> f <$> applyT t1 (c @@ LRCo_LR) lr <*> applyT t2 (c @@ LRCo_Co) co
                                      _          -> fail "not a left/right coercion."
{-# INLINE lrCoT #-}

-- | Transform all children of a coercion of the form: @LRCo@ 'LeftOrRight' 'Coercion'
lrCoAllR :: (ExtendPath c Crumb, Monad m) => Rewrite c m LeftOrRight -> Rewrite c m Coercion -> Rewrite c m Coercion
lrCoAllR r1 r2 = lrCoT r1 r2 LRCo
{-# INLINE lrCoAllR #-}

-- | Transform any children of a coercion of the form: @LRCo@ 'LeftOrRight' 'Coercion'
lrCoAnyR :: (ExtendPath c Crumb, MonadCatch m) => Rewrite c m LeftOrRight -> Rewrite c m Coercion -> Rewrite c m Coercion
lrCoAnyR r1 r2 = unwrapAnyR $ lrCoAllR (wrapAnyR r1) (wrapAnyR r2)
{-# INLINE lrCoAnyR #-}

-- | Transform one child of a coercion of the form: @LRCo@ 'LeftOrRight' 'Coercion'
lrCoOneR :: (ExtendPath c Crumb, MonadCatch m) => Rewrite c m LeftOrRight -> Rewrite c m Coercion -> Rewrite c m Coercion
lrCoOneR r1 r2 = unwrapOneR $ lrCoAllR (wrapOneR r1) (wrapOneR r2)
{-# INLINE lrCoOneR #-}


-- | Transform a coercion of the form: @InstCo@ 'Coercion' 'Type'
instCoT :: (ExtendPath c Crumb, Monad m) => Transform c m Coercion a1 -> Transform c m Type a2 -> (a1 -> a2 -> b) -> Transform c m Coercion b
instCoT t1 t2 f = transform $ \ c -> \case
                                          InstCo co ty -> f <$> applyT t1 (c @@ InstCo_Co) co <*> applyT t2 (c @@ InstCo_Type) ty
                                          _            -> fail "not a coercion instantiation."
{-# INLINE instCoT #-}

-- | Rewrite all children of a coercion of the form: @InstCo@ 'Coercion' 'Type'
instCoAllR :: (ExtendPath c Crumb, Monad m) => Rewrite c m Coercion -> Rewrite c m Type -> Rewrite c m Coercion
instCoAllR r1 r2 = instCoT r1 r2 InstCo
{-# INLINE instCoAllR #-}

-- | Rewrite any children of a coercion of the form: @InstCo@ 'Coercion' 'Type'
instCoAnyR :: (ExtendPath c Crumb, MonadCatch m) => Rewrite c m Coercion -> Rewrite c m Type -> Rewrite c m Coercion
instCoAnyR r1 r2 = unwrapAnyR $ instCoAllR (wrapAnyR r1) (wrapAnyR r2)
{-# INLINE instCoAnyR #-}

-- | Rewrite one child of a coercion of the form: @InstCo@ 'Coercion' 'Type'
instCoOneR :: (ExtendPath c Crumb, MonadCatch m) => Rewrite c m Coercion -> Rewrite c m Type -> Rewrite c m Coercion
instCoOneR r1 r2 = unwrapOneR $ instCoAllR (wrapOneR r1) (wrapOneR r2)
{-# INLINE instCoOneR #-}

-- | Transform a coercion of the form: @SubCo@ 'Coercion'
subCoT :: (ExtendPath c Crumb, Monad m) => Transform c m Coercion b -> Transform c m Coercion b
subCoT t = transform $ \ c -> \case
                                   SubCo co -> applyT t (c @@ SubCo_Co) co
                                   _        -> fail "not a sub coercion."
{-# INLINE subCoT #-}

-- | Rewrite the 'Coercion' child of a coercion of the form: @SubCo@ 'Coercion'
subCoR :: (ExtendPath c Crumb, Monad m) => Rewrite c m Coercion -> Rewrite c m Coercion
subCoR r = subCoT (SubCo <$> r)
{-# INLINE subCoR #-}

-- | Transform a coercion of the form: @UnivCo@ 'FastString' 'Role' 'Type' 'Type'
univCoT :: (ExtendPath c Crumb, Monad m) => Transform c m Type a1 -> Transform c m Type a2 -> (FastString -> Role -> a1 -> a2 -> b) -> Transform c m Coercion b
univCoT t1 t2 f = transform $ \ c -> \case
                                     UnivCo s r dom ran -> f s r <$> applyT t1 (c @@ UnivCo_Dom) dom <*> applyT t2 (c @@ UnivCo_Ran) ran
                                     _         -> fail "not a universal coercion."
{-# INLINE univCoT #-}

-- | Rewrite all children of a coercion of the form: @UnivCo@ 'FastString' 'Role' 'Type' 'Type'
univCoAllR :: (ExtendPath c Crumb, Monad m) => Rewrite c m Type -> Rewrite c m Type -> Rewrite c m Coercion
univCoAllR r1 r2 = univCoT r1 r2 UnivCo
{-# INLINE univCoAllR #-}

-- | Rewrite any children of a coercion of the form: @UnivCo@ 'FastString' 'Role' 'Type' 'Type'
univCoAnyR :: (ExtendPath c Crumb, MonadCatch m) => Rewrite c m Type -> Rewrite c m Type -> Rewrite c m Coercion
univCoAnyR r1 r2 = unwrapAnyR $ univCoAllR (wrapAnyR r1) (wrapAnyR r2)
{-# INLINE univCoAnyR #-}

-- | Rewrite one child of a coercion of the form: @UnivCo@ 'FastString' 'Role' 'Type' 'Type'
univCoOneR :: (ExtendPath c Crumb, MonadCatch m) => Rewrite c m Type -> Rewrite c m Type -> Rewrite c m Coercion
univCoOneR r1 r2 = unwrapOneR $ univCoAllR (wrapOneR r1) (wrapOneR r2)
{-# INLINE univCoOneR #-}

---------------------------------------------------------------------

-- | Transform a clause of the form: @Conj@ 'Clause' 'Clause'
conjT :: (ExtendPath c Crumb, Monad m) => Transform c m Clause a1 -> Transform c m Clause a2 -> (a1 -> a2 -> b) -> Transform c m Clause b
conjT t1 t2 f = transform $ \ c -> \case
                                     Conj q1 q2 -> f <$> applyT t1 (c @@ Conj_Lhs) q1 <*> applyT t2 (c @@ Conj_Rhs) q2
                                     _          -> fail "not a conjunction."
{-# INLINE conjT #-}

-- | Rewrite all children of a clause of the form: : @Conj@ 'Clause' 'Clause'
conjAllR :: (ExtendPath c Crumb, Monad m) => Rewrite c m Clause -> Rewrite c m Clause -> Rewrite c m Clause
conjAllR r1 r2 = conjT r1 r2 Conj
{-# INLINE conjAllR #-}


-- | Transform a clause of the form: @Disj@ 'Clause' 'Clause'
disjT :: (ExtendPath c Crumb, Monad m) => Transform c m Clause a1 -> Transform c m Clause a2 -> (a1 -> a2 -> b) -> Transform c m Clause b
disjT t1 t2 f = transform $ \ c -> \case
                                     Disj q1 q2 -> f <$> applyT t1 (c @@ Disj_Lhs) q1 <*> applyT t2 (c @@ Disj_Rhs) q2
                                     _          -> fail "not a disjunction."
{-# INLINE disjT #-}

-- | Rewrite all children of a clause of the form: : @Disj@ 'Clause' 'Clause'
disjAllR :: (ExtendPath c Crumb, Monad m) => Rewrite c m Clause -> Rewrite c m Clause -> Rewrite c m Clause
disjAllR r1 r2 = disjT r1 r2 Disj
{-# INLINE disjAllR #-}


-- | Transform a clause of the form: @Impl@ 'LemmaName' 'Clause' 'Clause'
implT :: (ExtendPath c Crumb, LemmaContext c, Monad m)
      => Transform c m Clause a1 -> Transform c m Clause a2 -> (LemmaName -> a1 -> a2 -> b) -> Transform c m Clause b
implT t1 t2 f = transform $ \ c -> \case
                                     Impl nm q1 q2 -> let l = Lemma q1 BuiltIn NotUsed
                                                      in f nm <$> applyT t1 (c @@ Impl_Lhs) q1
                                                              <*> applyT t2 (addAntecedent nm l c @@ Impl_Rhs) q2
                                     _          -> fail "not an implication."
{-# INLINE implT #-}

-- | Rewrite all children of a clause of the form: : @Impl@ 'Clause' 'Clause'
implAllR :: (ExtendPath c Crumb, LemmaContext c, Monad m)
         => Rewrite c m Clause -> Rewrite c m Clause -> Rewrite c m Clause
implAllR r1 r2 = implT r1 r2 Impl
{-# INLINE implAllR #-}

-- | Transform a clause of the form: @Equiv@ 'CoreExpr' 'CoreExpr'
equivT :: (ExtendPath c Crumb, Monad m) => Transform c m CoreExpr a1 -> Transform c m CoreExpr a2 -> (a1 -> a2 -> b) -> Transform c m Clause b
equivT t1 t2 f = transform $ \ c -> \case
                                     Equiv e1 e2 -> f <$> applyT t1 (c @@ Eq_Lhs) e1 <*> applyT t2 (c @@ Eq_Rhs) e2
                                     _           -> fail "not an equivalence."
{-# INLINE equivT #-}

-- | Rewrite all children of a clause of the form: : @Equiv@ 'CoreExpr' 'CoreExpr'
equivAllR :: (ExtendPath c Crumb, Monad m) => Rewrite c m CoreExpr -> Rewrite c m CoreExpr -> Rewrite c m Clause
equivAllR r1 r2 = equivT r1 r2 Equiv
{-# INLINE equivAllR #-}

---------------------------------------------------------------------

-- | Transform a clause of the form: @Forall@ 'CoreBndr' 'Clause'
forallT :: (ExtendPath c Crumb, AddBindings c, ReadPath c Crumb, Monad m)
        => Transform c m CoreBndr a1 -> Transform c m Clause a2 -> (a1 -> a2 -> b) -> Transform c m Clause b
forallT t1 t2 f = transform $ \ c -> \case
                                        Forall b cl -> let c' = addLambdaBinding b c
                                                       in f <$> applyT t1 c b <*> applyT t2 (c' @@ Forall_Body) cl
                                        _           -> fail "not a quantified clause."
{-# INLINE forallT #-}

-- | Rewrite the a clause of the form: @Forall@ 'CoreBndr' 'Clause'
forallR :: (ExtendPath c Crumb, AddBindings c, ReadPath c Crumb, Monad m)
        => Rewrite c m CoreBndr -> Rewrite c m Clause -> Rewrite c m Clause
forallR r1 r2 = forallT r1 r2 Forall
{-# INLINE forallR #-}

-- | Transform a clause with nested forall quantifiers.
forallsT :: (ExtendPath c Crumb, AddBindings c, ReadPath c Crumb, Monad m)
         => Transform c m [CoreBndr] a1 -> Transform c m Clause a2 -> (a1 -> a2 -> b) -> Transform c m Clause b
forallsT t1 t2 f = transform $ \ c e -> case collectQs e of
                                            (bs@(_:_),cl) ->
                                                let c' = foldl (\ctxt b -> addLambdaBinding b ctxt @@ Forall_Body) c bs
                                                in f <$> applyT t1 c bs <*> applyT t2 c' cl
                                            _             -> fail "not a quantified clause."
{-# INLINE forallsT #-}

-- | Rewrite the a clause with nested forall quantifiers.
forallsR :: (ExtendPath c Crumb, AddBindings c, ReadPath c Crumb, Monad m)
         => Rewrite c m [CoreBndr] -> Rewrite c m Clause -> Rewrite c m Clause
forallsR r1 r2 = forallsT r1 r2 mkForall
{-# INLINE forallsR #-}

---------------------------------------------------------------------

instance HasDynFlags m => HasDynFlags (Transform c m a) where
    getDynFlags = constT getDynFlags

---------------------------------------------------------------------

-- Useful for utilities which are Transforms for a reason, but don't use their input.
inContextM :: c -> Transform c m () a -> m a
inContextM c t = applyT t c ()

