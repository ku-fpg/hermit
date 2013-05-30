{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, TupleSections, LambdaCase, InstanceSigs, ScopedTypeVariables #-}

module Language.HERMIT.Kure
       (
       -- * KURE

       -- | All the required functionality of KURE is exported here, so other modules do not need to import KURE directly.
         module Language.KURE
       , module Language.KURE.BiTranslate
       , module Language.KURE.Lens
       -- * Synonyms
       -- | In HERMIT, 'Translate', 'Rewrite' and 'Lens' always operate on the same context and monad.
       , TranslateH
       , RewriteH
       , BiRewriteH
       , LensH

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
       -- * Congruence Combinators for Traversing Types
       , tyVarT
       , litTyT
       , appTyT, appTyAllR, appTyAnyR, appTyOneR
       , funTyT, funTyAllR, funTyAnyR, funTyOneR
       , forallTyT, forallTyR
       , tyConAppT, tyConAppAllR, tyConAppAnyR, tyConAppOneR

       -- * Promotion Combinators
       -- ** Rewrite Promotions
       , promoteModGutsR
       , promoteProgR
       , promoteBindR
       , promoteDefR
       , promoteExprR
       , promoteAltR
       -- ** BiRewrite Promotions
       , promoteExprBiR
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
import Language.KURE.BiTranslate
import Language.KURE.Lens

import Language.HERMIT.GHC
import Language.HERMIT.Core
import Language.HERMIT.Context
import Language.HERMIT.Monad

import Control.Monad

---------------------------------------------------------------------

type TranslateH a b = Translate HermitC HermitM a b
type RewriteH a     = Rewrite   HermitC HermitM a
type BiRewriteH a   = BiRewrite HermitC HermitM a
type LensH a b      = Lens      HermitC HermitM a b

-- I find it annoying that Applicative is not a superclass of Monad.
(<$>) :: Monad m => (a -> b) -> m a -> m b
(<$>) = liftM
{-# INLINE (<$>) #-}

(<*>) :: Monad m => m (a -> b) -> m a -> m b
(<*>) = ap
{-# INLINE (<*>) #-}

---------------------------------------------------------------------

instance Injection ModGuts Core where

  inject :: ModGuts -> Core
  inject = GutsCore
  {-# INLINE inject #-}

  project :: Core -> Maybe ModGuts
  project (GutsCore guts) = Just guts
  project _                  = Nothing
  {-# INLINE project #-}


instance Injection CoreProg Core where

  inject :: CoreProg -> Core
  inject = ProgCore
  {-# INLINE inject #-}

  project :: Core -> Maybe CoreProg
  project (ProgCore bds) = Just bds
  project _              = Nothing
  {-# INLINE project #-}


instance Injection CoreBind Core where

  inject :: CoreBind -> Core
  inject = BindCore
  {-# INLINE inject #-}

  project :: Core -> Maybe CoreBind
  project (BindCore bnd)  = Just bnd
  project _               = Nothing
  {-# INLINE project #-}


instance Injection CoreDef Core where

  inject :: CoreDef -> Core
  inject = DefCore
  {-# INLINE inject #-}

  project :: Core -> Maybe CoreDef
  project (DefCore def) = Just def
  project _             = Nothing
  {-# INLINE project #-}


instance Injection CoreAlt Core where

  inject :: CoreAlt -> Core
  inject = AltCore
  {-# INLINE inject #-}

  project :: Core -> Maybe CoreAlt
  project (AltCore expr) = Just expr
  project _              = Nothing
  {-# INLINE project #-}


instance Injection CoreExpr Core where

  inject :: CoreExpr -> Core
  inject = ExprCore
  {-# INLINE inject #-}

  project :: Core -> Maybe CoreExpr
  project (ExprCore expr) = Just expr
  project _               = Nothing
  {-# INLINE project #-}

---------------------------------------------------------------------

instance (PathContext c, BindingContext c) => Walker c Core where

  allR :: forall m. MonadCatch m => Rewrite c m Core -> Rewrite c m Core
  allR r = prefixFailMsg "allR failed: " $
           rewrite $ \ c -> \case
             GutsCore guts  -> inject <$> apply allRmodguts c guts
             ProgCore p     -> inject <$> apply allRprog c p
             BindCore bn    -> inject <$> apply allRbind c bn
             DefCore def    -> inject <$> apply allRdef c def
             AltCore alt    -> inject <$> apply allRalt c alt
             ExprCore e     -> inject <$> apply allRexpr c e
    where
      allRmodguts :: MonadCatch m => Rewrite c m ModGuts
      allRmodguts = modGutsR (extractR r)
      {-# INLINE allRmodguts #-}

      allRprog :: MonadCatch m => Rewrite c m CoreProg
      allRprog = readerT $ \case
                              ProgCons _ _ -> progConsAllR (extractR r) (extractR r)
                              _            -> idR
      {-# INLINE allRprog #-}

      allRbind :: MonadCatch m => Rewrite c m CoreBind
      allRbind = readerT $ \case
                              NonRec _ _  -> nonRecR (extractR r)
                              Rec _       -> recAllR (const $ extractR r)
      {-# INLINE allRbind #-}

      allRdef :: MonadCatch m => Rewrite c m CoreDef
      allRdef = defR (extractR r)
      {-# INLINE allRdef #-}

      allRalt :: MonadCatch m => Rewrite c m CoreAlt
      allRalt = altR (extractR r)
      {-# INLINE allRalt #-}

      allRexpr :: MonadCatch m => Rewrite c m CoreExpr
      allRexpr = readerT $ \case
                              App _ _      -> appAllR (extractR r) (extractR r)
                              Lam _ _      -> lamR (extractR r)
                              Let _ _      -> letAllR (extractR r) (extractR r)
                              Case _ _ _ _ -> caseAllR (extractR r) (const $ extractR r)
                              Cast _ _     -> castR (extractR r)
                              Tick _ _     -> tickR (extractR r)
                              _            -> idR
      {-# INLINE allRexpr #-}

-- NOTE: I tried telling GHC to inline allR and compilation hit the (default) simplifier tick limit.
-- TODO: Investigate whether that was achieving useful optimisations.

---------------------------------------------------------------------

-- | Translate a module.
--   Slightly different to the other congruence combinators: it passes in /all/ of the original to the reconstruction function.
modGutsT :: (PathContext c, Monad m) => Translate c m CoreProg a -> (ModGuts -> a -> b) -> Translate c m ModGuts b
modGutsT t f = translate $ \ c guts -> f guts <$> apply t (c @@ 0) (bindsToProg $ mg_binds guts)
{-# INLINE modGutsT #-}

-- | Rewrite the 'CoreProg' child of a module.
modGutsR :: (PathContext c, Monad m) => Rewrite c m CoreProg -> Rewrite c m ModGuts
modGutsR r = modGutsT r (\ guts p -> guts {mg_binds = progToBinds p})
{-# INLINE modGutsR #-}

---------------------------------------------------------------------

-- | Translate an empty list.
progNilT :: Monad m => b -> Translate c m CoreProg b
progNilT b = contextfreeT $ \case
                               ProgNil       -> return b
                               ProgCons _ _  -> fail "not an empty program node."
{-# INLINE progNilT #-}

-- | Translate a program of the form: ('CoreBind' @:@ 'CoreProg')
progConsT :: (PathContext c, BindingContext c, Monad m) => Translate c m CoreBind a1 -> Translate c m CoreProg a2 -> (a1 -> a2 -> b) -> Translate c m CoreProg b
progConsT t1 t2 f = translate $ \ c -> \case
                                          ProgCons bd p -> f <$> apply t1 (c @@ 0) bd <*> apply t2 (addBindingGroup bd c @@ 1) p
                                          _             -> fail "not a non-empty program node."
{-# INLINE progConsT #-}

-- | Rewrite all children of a program of the form: ('CoreBind' @:@ 'CoreProg')
progConsAllR :: (PathContext c, BindingContext c, Monad m) => Rewrite c m CoreBind -> Rewrite c m CoreProg -> Rewrite c m CoreProg
progConsAllR r1 r2 = progConsT r1 r2 ProgCons
{-# INLINE progConsAllR #-}

-- | Rewrite any children of a program of the form: ('CoreBind' @:@ 'CoreProg')
progConsAnyR :: (PathContext c, BindingContext c, MonadCatch m) => Rewrite c m CoreBind -> Rewrite c m CoreProg -> Rewrite c m CoreProg
progConsAnyR r1 r2 = unwrapAnyR $ progConsAllR (wrapAnyR r1) (wrapAnyR r2)
{-# INLINE progConsAnyR #-}

-- | Rewrite one child of a program of the form: ('CoreBind' @:@ 'CoreProg')
progConsOneR :: (PathContext c, BindingContext c, MonadCatch m) => Rewrite c m CoreBind -> Rewrite c m CoreProg -> Rewrite c m CoreProg
progConsOneR r1 r2 = unwrapOneR $  progConsAllR (wrapOneR r1) (wrapOneR r2)
{-# INLINE progConsOneR #-}

---------------------------------------------------------------------

-- | Translate a binding group of the form: @NonRec@ 'Var' 'CoreExpr'
nonRecT :: (PathContext c, Monad m) => Translate c m CoreExpr a -> (Var -> a -> b) -> Translate c m CoreBind b
nonRecT t f = translate $ \ c -> \case
                                    NonRec v e -> f v <$> apply t (c @@ 0) e
                                    _          -> fail "not a non-recursive binding-group node."
{-# INLINE nonRecT #-}

-- | Rewrite the 'CoreExpr' child of a binding group of the form: @NonRec@ 'Var' 'CoreExpr'
nonRecR :: (PathContext c, Monad m) => Rewrite c m CoreExpr -> Rewrite c m CoreBind
nonRecR r = nonRecT r NonRec
{-# INLINE nonRecR #-}

-- | Translate a binding group of the form: @Rec@ ['CoreDef']
recT :: (PathContext c, BindingContext c, Monad m) => (Int -> Translate c m CoreDef a) -> ([a] -> b) -> Translate c m CoreBind b
recT t f = translate $ \ c -> \case
         Rec bds -> -- Notice how we add the scoping bindings here *before* descending into each individual definition.
                    let c' = addBindingGroup (Rec bds) c
                     in f <$> sequence [ apply (t n) (c' @@ n) (Def v e) -- here we convert from (Id,CoreExpr) to CoreDef
                                       | ((v,e),n) <- zip bds [0..]
                                       ]
         _       -> fail "not a recursive binding-group node."
{-# INLINE recT #-}

-- | Rewrite all children of a binding group of the form: @Rec@ ['CoreDef']
recAllR :: (PathContext c, BindingContext c, Monad m) => (Int -> Rewrite c m CoreDef) -> Rewrite c m CoreBind
recAllR rs = recT rs defsToRecBind
{-# INLINE recAllR #-}

-- | Rewrite any children of a binding group of the form: @Rec@ ['CoreDef']
recAnyR :: (PathContext c, BindingContext c, MonadCatch m) => (Int -> Rewrite c m CoreDef) -> Rewrite c m CoreBind
recAnyR rs = unwrapAnyR $ recAllR (wrapAnyR . rs)
{-# INLINE recAnyR #-}

-- | Rewrite one child of a binding group of the form: @Rec@ ['CoreDef']
recOneR :: (PathContext c, BindingContext c, MonadCatch m) => (Int -> Rewrite c m CoreDef) -> Rewrite c m CoreBind
recOneR rs = unwrapOneR $ recAllR (wrapOneR . rs)
{-# INLINE recOneR #-}

---------------------------------------------------------------------

-- | Translate a recursive definition of the form: @Def@ 'Id' 'CoreExpr'
defT :: (PathContext c, Monad m) => Translate c m CoreExpr a -> (Id -> a -> b) -> Translate c m CoreDef b
defT t f = translate $ \ c (Def v e) -> f v <$> apply t (c @@ 0) e
{-# INLINE defT #-}

-- | Rewrite the 'CoreExpr' child of a recursive definition of the form: @Def@ 'Id' 'CoreExpr'
defR :: (PathContext c, Monad m) => Rewrite c m CoreExpr -> Rewrite c m CoreDef
defR r = defT r Def
{-# INLINE defR #-}

---------------------------------------------------------------------

-- | Translate a case alternative of the form: ('AltCon', ['Var'], 'CoreExpr')
altT :: (PathContext c, BindingContext c, Monad m) => Translate c m CoreExpr a -> (AltCon -> [Var] -> a -> b) -> Translate c m CoreAlt b
altT t f = translate $ \ c (con,vs,e) -> f con vs <$> apply t (addAltBindings vs c @@ 0) e
{-# INLINE altT #-}

-- | Rewrite the 'CoreExpr' child of a case alternative of the form: ('AltCon', 'Id', 'CoreExpr')
altR :: (PathContext c, BindingContext c, Monad m) => Rewrite c m CoreExpr -> Rewrite c m CoreAlt
altR r = altT r (,,)
{-# INLINE altR #-}

---------------------------------------------------------------------

-- | Translate an expression of the form: @Var@ 'Id'
varT :: Monad m => (Id -> b) -> Translate c m CoreExpr b
varT f = contextfreeT $ \case
                           Var v -> return (f v)
                           _     -> fail "not a variable node."
{-# INLINE varT #-}

-- | Translate an expression of the form: @Lit@ 'Literal'
litT :: Monad m => (Literal -> b) -> Translate c m CoreExpr b
litT f = contextfreeT $ \case
                           Lit x -> return (f x)
                           _     -> fail "not a literal node."
{-# INLINE litT #-}

-- | Translate an expression of the form: @App@ 'CoreExpr' 'CoreExpr'
appT :: (PathContext c, Monad m) => Translate c m CoreExpr a1 -> Translate c m CoreExpr a2 -> (a1 -> a2 -> b) -> Translate c m CoreExpr b
appT t1 t2 f = translate $ \ c -> \case
                                     App e1 e2 -> f <$> apply t1 (c @@ 0) e1 <*> apply t2 (c @@ 1) e2
                                     _         -> fail "not an application node."
{-# INLINE appT #-}

-- | Rewrite all children of an expression of the form: @App@ 'CoreExpr' 'CoreExpr'
appAllR :: (PathContext c, Monad m) => Rewrite c m CoreExpr -> Rewrite c m CoreExpr -> Rewrite c m CoreExpr
appAllR r1 r2 = appT r1 r2 App
{-# INLINE appAllR #-}

-- | Rewrite any children of an expression of the form: @App@ 'CoreExpr' 'CoreExpr'
appAnyR :: (PathContext c, MonadCatch m) => Rewrite c m CoreExpr -> Rewrite c m CoreExpr -> Rewrite c m CoreExpr
appAnyR r1 r2 = unwrapAnyR $ appAllR (wrapAnyR r1) (wrapAnyR r2)
{-# INLINE appAnyR #-}

-- | Rewrite one child of an expression of the form: @App@ 'CoreExpr' 'CoreExpr'
appOneR :: (PathContext c, MonadCatch m) => Rewrite c m CoreExpr -> Rewrite c m CoreExpr -> Rewrite c m CoreExpr
appOneR r1 r2 = unwrapOneR $ appAllR (wrapOneR r1) (wrapOneR r2)
{-# INLINE appOneR #-}

-- | Translate an expression of the form: @Lam@ 'Var' 'CoreExpr'
lamT :: (PathContext c, BindingContext c, Monad m) => Translate c m CoreExpr a -> (Var -> a -> b) -> Translate c m CoreExpr b
lamT t f = translate $ \ c -> \case
                                 Lam v e -> f v <$> apply t (addLambdaBinding v c @@ 0) e
                                 _       -> fail "not a lambda node."
{-# INLINE lamT #-}

-- | Rewrite the 'CoreExpr' child of an expression of the form: @Lam@ 'Var' 'CoreExpr'
lamR :: (PathContext c, BindingContext c, Monad m) => Rewrite c m CoreExpr -> Rewrite c m CoreExpr
lamR r = lamT r Lam
{-# INLINE lamR #-}

-- | Translate an expression of the form: @Let@ 'CoreBind' 'CoreExpr'
letT :: (PathContext c, BindingContext c, Monad m) => Translate c m CoreBind a1 -> Translate c m CoreExpr a2 -> (a1 -> a2 -> b) -> Translate c m CoreExpr b
letT t1 t2 f = translate $ \ c -> \case
        Let bds e -> -- Note we use the *original* context for the binding group.
                     -- If the bindings are recursive, they will be added to the context by recT.
                     f <$> apply t1 (c @@ 0) bds <*> apply t2 (addBindingGroup bds c @@ 1) e
        _         -> fail "not a let node."
{-# INLINE letT #-}

-- | Rewrite all children of an expression of the form: @Let@ 'CoreBind' 'CoreExpr'
letAllR :: (PathContext c, BindingContext c, Monad m) => Rewrite c m CoreBind -> Rewrite c m CoreExpr -> Rewrite c m CoreExpr
letAllR r1 r2 = letT r1 r2 Let
{-# INLINE letAllR #-}

-- | Rewrite any children of an expression of the form: @Let@ 'CoreBind' 'CoreExpr'
letAnyR :: (PathContext c, BindingContext c, MonadCatch m) => Rewrite c m CoreBind -> Rewrite c m CoreExpr -> Rewrite c m CoreExpr
letAnyR r1 r2 = unwrapAnyR $ letAnyR (wrapAnyR r1) (wrapAnyR r2)
{-# INLINE letAnyR #-}

-- | Rewrite one child of an expression of the form: @Let@ 'CoreBind' 'CoreExpr'
letOneR :: (PathContext c, BindingContext c, MonadCatch m) => Rewrite c m CoreBind -> Rewrite c m CoreExpr -> Rewrite c m CoreExpr
letOneR r1 r2 = unwrapOneR $ letOneR (wrapOneR r1) (wrapOneR r2)
{-# INLINE letOneR #-}


-- | Translate an expression of the form: @Case@ 'CoreExpr' 'Id' 'Type' ['CoreAlt']
caseT :: (PathContext c, BindingContext c, Monad m) => Translate c m CoreExpr a1 -> (Int -> Translate c m CoreAlt a2) -> (a1 -> Id -> Type -> [a2] -> b) -> Translate c m CoreExpr b
caseT t ts f = translate $ \ c -> \case
         Case e x ty alts -> f <$> apply t (c @@ 0) e
                               <*> return x
                               <*> return ty
                               <*> sequence [ apply (ts n) (addCaseBinding (x,e,alt) c @@ (n+1)) alt
                                            | (alt,n) <- zip alts [0..]
                                            ]
         _                -> fail "not a case node."
{-# INLINE caseT #-}

-- | Rewrite all children of an expression of the form: @Case@ 'CoreExpr' 'Id' 'Type' ['CoreAlt']
caseAllR :: (PathContext c, BindingContext c, Monad m) => Rewrite c m CoreExpr -> (Int -> Rewrite c m CoreAlt) -> Rewrite c m CoreExpr
caseAllR r rs = caseT r rs Case
{-# INLINE caseAllR #-}

-- | Rewrite any children of an expression of the form: @Case@ 'CoreExpr' 'Id' 'Type' ['CoreAlt']
caseAnyR :: (PathContext c, BindingContext c, MonadCatch m) => Rewrite c m CoreExpr -> (Int -> Rewrite c m CoreAlt) -> Rewrite c m CoreExpr
caseAnyR r rs = unwrapAnyR $ caseAllR (wrapAnyR r) (wrapAnyR . rs)
{-# INLINE caseAnyR #-}

-- | Rewrite one child of an expression of the form: @Case@ 'CoreExpr' 'Id' 'Type' ['CoreAlt']
caseOneR :: (PathContext c, BindingContext c, MonadCatch m) => Rewrite c m CoreExpr -> (Int -> Rewrite c m CoreAlt) -> Rewrite c m CoreExpr
caseOneR r rs = unwrapOneR $ caseAllR (wrapOneR r) (wrapOneR . rs)
{-# INLINE caseOneR #-}

-- | Translate an expression of the form: @Cast@ 'CoreExpr' 'Coercion'
castT :: (PathContext c, Monad m) => Translate c m CoreExpr a -> (a -> Coercion -> b) -> Translate c m CoreExpr b
castT t f = translate $ \ c -> \case
                                  Cast e cast -> f <$> apply t (c @@ 0) e <*> return cast
                                  _           -> fail "not a cast node."
{-# INLINE castT #-}

-- | Rewrite the 'CoreExpr' child of an expression of the form: @Cast@ 'CoreExpr' 'Coercion'
castR :: (PathContext c, Monad m) => Rewrite c m CoreExpr -> Rewrite c m CoreExpr
castR r = castT r Cast
{-# INLINE castR #-}

-- | Translate an expression of the form: @Tick@ 'CoreTickish' 'CoreExpr'
tickT :: (PathContext c, Monad m) => Translate c m CoreExpr a -> (CoreTickish -> a -> b) -> Translate c m CoreExpr b
tickT t f = translate $ \ c -> \case
        Tick tk e -> f tk <$> apply t (c @@ 0) e
        _         -> fail "not a tick node."
{-# INLINE tickT #-}

-- | Rewrite the 'CoreExpr' child of an expression of the form: @Tick@ 'CoreTickish' 'CoreExpr'
tickR :: (PathContext c, Monad m) => Rewrite c m CoreExpr -> Rewrite c m CoreExpr
tickR r = tickT r Tick
{-# INLINE tickR #-}

-- | Translate an expression of the form: @Type@ 'Type'
typeT :: Monad m => (Type -> b) -> Translate c m CoreExpr b
typeT f = contextfreeT $ \case
                            Type t -> return (f t)
                            _      -> fail "not a type node."
{-# INLINE typeT #-}

-- | Translate an expression of the form: @Coercion@ 'Coercion'
coercionT :: Monad m => (Coercion -> b) -> Translate c m CoreExpr b
coercionT f = contextfreeT $ \case
                                Coercion co -> return (f co)
                                _           -> fail "not a coercion node."
{-# INLINE coercionT #-}

---------------------------------------------------------------------

-- Some composite congruence combinators to export.

-- | Translate a binding group of the form: @Rec@ [('Id', 'CoreExpr')]
recDefT :: (PathContext c, BindingContext c, Monad m) => (Int -> Translate c m CoreExpr a1) -> ([(Id,a1)] -> b) -> Translate c m CoreBind b
recDefT ts = recT (\ n -> defT (ts n) (,))
{-# INLINE recDefT #-}

-- | Rewrite all children of a binding group of the form: @Rec@ [('Id', 'CoreExpr')]
recDefAllR :: (PathContext c, BindingContext c, Monad m) => (Int -> Rewrite c m CoreExpr) -> Rewrite c m CoreBind
recDefAllR rs = recAllR (\ n -> defR (rs n))
{-# INLINE recDefAllR #-}

-- | Rewrite any children of a binding group of the form: @Rec@ [('Id', 'CoreExpr')]
recDefAnyR :: (PathContext c, BindingContext c, MonadCatch m) => (Int -> Rewrite c m CoreExpr) -> Rewrite c m CoreBind
recDefAnyR rs = recAnyR (\ n -> defR (rs n))
{-# INLINE recDefAnyR #-}

-- | Rewrite one child of a binding group of the form: @Rec@ [('Id', 'CoreExpr')]
recDefOneR :: (PathContext c, BindingContext c, MonadCatch m) => (Int -> Rewrite c m CoreExpr) -> Rewrite c m CoreBind
recDefOneR rs = recOneR (\ n -> defR (rs n))
{-# INLINE recDefOneR #-}


-- | Translate a program of the form: (@NonRec@ 'Var' 'CoreExpr') @:@ 'CoreProg'
consNonRecT :: (PathContext c, BindingContext c, Monad m) => Translate c m CoreExpr a1 -> Translate c m CoreProg a2 -> (Var -> a1 -> a2 -> b) -> Translate c m CoreProg b
consNonRecT t1 t2 f = progConsT (nonRecT t1 (,)) t2 (uncurry f)
{-# INLINE consNonRecT #-}

-- | Rewrite all children of an expression of the form: (@NonRec@ 'Var' 'CoreExpr') @:@ 'CoreProg'
consNonRecAllR :: (PathContext c, BindingContext c, Monad m) => Rewrite c m CoreExpr -> Rewrite c m CoreProg -> Rewrite c m CoreProg
consNonRecAllR r1 r2 = progConsAllR (nonRecR r1) r2
{-# INLINE consNonRecAllR #-}

-- | Rewrite any children of an expression of the form: (@NonRec@ 'Var' 'CoreExpr') @:@ 'CoreProg'
consNonRecAnyR :: (PathContext c, BindingContext c, MonadCatch m) => Rewrite c m CoreExpr -> Rewrite c m CoreProg -> Rewrite c m CoreProg
consNonRecAnyR r1 r2 = progConsAnyR (nonRecR r1) r2
{-# INLINE consNonRecAnyR #-}

-- | Rewrite one child of an expression of the form: (@NonRec@ 'Var' 'CoreExpr') @:@ 'CoreProg'
consNonRecOneR :: (PathContext c, BindingContext c, MonadCatch m) => Rewrite c m CoreExpr -> Rewrite c m CoreProg -> Rewrite c m CoreProg
consNonRecOneR r1 r2 = progConsOneR (nonRecR r1) r2
{-# INLINE consNonRecOneR #-}


-- | Translate an expression of the form: (@Rec@ ['CoreDef']) @:@ 'CoreProg'
consRecT :: (PathContext c, BindingContext c, Monad m) => (Int -> Translate c m CoreDef a1) -> Translate c m CoreProg a2 -> ([a1] -> a2 -> b) -> Translate c m CoreProg b
consRecT ts t = progConsT (recT ts id) t
{-# INLINE consRecT #-}

-- | Rewrite all children of an expression of the form: (@Rec@ ['CoreDef']) @:@ 'CoreProg'
consRecAllR :: (PathContext c, BindingContext c, Monad m) => (Int -> Rewrite c m CoreDef) -> Rewrite c m CoreProg -> Rewrite c m CoreProg
consRecAllR rs r = progConsAllR (recAllR rs) r
{-# INLINE consRecAllR #-}

-- | Rewrite any children of an expression of the form: (@Rec@ ['CoreDef']) @:@ 'CoreProg'
consRecAnyR :: (PathContext c, BindingContext c, MonadCatch m) => (Int -> Rewrite c m CoreDef) -> Rewrite c m CoreProg -> Rewrite c m CoreProg
consRecAnyR rs r = progConsAnyR (recAnyR rs) r
{-# INLINE consRecAnyR #-}

-- | Rewrite one child of an expression of the form: (@Rec@ ['CoreDef']) @:@ 'CoreProg'
consRecOneR :: (PathContext c, BindingContext c, MonadCatch m) => (Int -> Rewrite c m CoreDef) -> Rewrite c m CoreProg -> Rewrite c m CoreProg
consRecOneR rs r = progConsOneR (recOneR rs) r
{-# INLINE consRecOneR #-}


-- | Translate an expression of the form: (@Rec@ [('Id', 'CoreExpr')]) @:@ 'CoreProg'
consRecDefT :: (PathContext c, BindingContext c, Monad m) => (Int -> Translate c m CoreExpr a1) -> Translate c m CoreProg a2 -> ([(Id,a1)] -> a2 -> b) -> Translate c m CoreProg b
consRecDefT ts t = consRecT (\ n -> defT (ts n) (,)) t
{-# INLINE consRecDefT #-}

-- | Rewrite all children of an expression of the form: (@Rec@ [('Id', 'CoreExpr')]) @:@ 'CoreProg'
consRecDefAllR :: (PathContext c, BindingContext c, Monad m) => (Int -> Rewrite c m CoreExpr) -> Rewrite c m CoreProg -> Rewrite c m CoreProg
consRecDefAllR rs r = consRecAllR (\ n -> defR (rs n)) r
{-# INLINE consRecDefAllR #-}

-- | Rewrite any children of an expression of the form: (@Rec@ [('Id', 'CoreExpr')]) @:@ 'CoreProg'
consRecDefAnyR :: (PathContext c, BindingContext c, MonadCatch m) => (Int -> Rewrite c m CoreExpr) -> Rewrite c m CoreProg -> Rewrite c m CoreProg
consRecDefAnyR rs r = consRecAnyR (\ n -> defR (rs n)) r
{-# INLINE consRecDefAnyR #-}

-- | Rewrite one child of an expression of the form: (@Rec@ [('Id', 'CoreExpr')]) @:@ 'CoreProg'
consRecDefOneR :: (PathContext c, BindingContext c, MonadCatch m) => (Int -> Rewrite c m CoreExpr) -> Rewrite c m CoreProg -> Rewrite c m CoreProg
consRecDefOneR rs r = consRecOneR (\ n -> defR (rs n)) r
{-# INLINE consRecDefOneR #-}


-- | Translate an expression of the form: @Let@ (@NonRec@ 'Var' 'CoreExpr') 'CoreExpr'
letNonRecT :: (PathContext c, BindingContext c, Monad m) => Translate c m CoreExpr a1 -> Translate c m CoreExpr a2 -> (Var -> a1 -> a2 -> b) -> Translate c m CoreExpr b
letNonRecT t1 t2 f = letT (nonRecT t1 (,)) t2 (uncurry f)
{-# INLINE letNonRecT #-}

-- | Rewrite all children of an expression of the form: @Let@ (@NonRec@ 'Var' 'CoreExpr') 'CoreExpr'
letNonRecAllR :: (PathContext c, BindingContext c, Monad m) => Rewrite c m CoreExpr -> Rewrite c m CoreExpr -> Rewrite c m CoreExpr
letNonRecAllR r1 r2 = letAllR (nonRecR r1) r2
{-# INLINE letNonRecAllR #-}

-- | Rewrite any children of an expression of the form: @Let@ (@NonRec@ 'Var' 'CoreExpr') 'CoreExpr'
letNonRecAnyR :: (PathContext c, BindingContext c, MonadCatch m) => Rewrite c m CoreExpr -> Rewrite c m CoreExpr -> Rewrite c m CoreExpr
letNonRecAnyR r1 r2 = letAnyR (nonRecR r1) r2
{-# INLINE letNonRecAnyR #-}

-- | Rewrite one child of an expression of the form: @Let@ (@NonRec@ 'Var' 'CoreExpr') 'CoreExpr'
letNonRecOneR :: (PathContext c, BindingContext c, MonadCatch m) => Rewrite c m CoreExpr -> Rewrite c m CoreExpr -> Rewrite c m CoreExpr
letNonRecOneR r1 r2 = letOneR (nonRecR r1) r2
{-# INLINE letNonRecOneR #-}


-- | Translate an expression of the form: @Let@ (@Rec@ ['CoreDef']) 'CoreExpr'
letRecT :: (PathContext c, BindingContext c, Monad m) => (Int -> Translate c m CoreDef a1) -> Translate c m CoreExpr a2 -> ([a1] -> a2 -> b) -> Translate c m CoreExpr b
letRecT ts t = letT (recT ts id) t
{-# INLINE letRecT #-}

-- | Rewrite all children of an expression of the form: @Let@ (@Rec@ ['CoreDef']) 'CoreExpr'
letRecAllR :: (PathContext c, BindingContext c, Monad m) => (Int -> Rewrite c m CoreDef) -> Rewrite c m CoreExpr -> Rewrite c m CoreExpr
letRecAllR rs r = letAllR (recAllR rs) r
{-# INLINE letRecAllR #-}

-- | Rewrite any children of an expression of the form: @Let@ (@Rec@ ['CoreDef']) 'CoreExpr'
letRecAnyR :: (PathContext c, BindingContext c, MonadCatch m) => (Int -> Rewrite c m CoreDef) -> Rewrite c m CoreExpr -> Rewrite c m CoreExpr
letRecAnyR rs r = letAnyR (recAnyR rs) r
{-# INLINE letRecAnyR #-}

-- | Rewrite one child of an expression of the form: @Let@ (@Rec@ ['CoreDef']) 'CoreExpr'
letRecOneR :: (PathContext c, BindingContext c, MonadCatch m) => (Int -> Rewrite c m CoreDef) -> Rewrite c m CoreExpr -> Rewrite c m CoreExpr
letRecOneR rs r = letOneR (recOneR rs) r
{-# INLINE letRecOneR #-}


-- | Translate an expression of the form: @Let@ (@Rec@ [('Id', 'CoreExpr')]) 'CoreExpr'
letRecDefT :: (PathContext c, BindingContext c, Monad m) => (Int -> Translate c m CoreExpr a1) -> Translate c m CoreExpr a2 -> ([(Id,a1)] -> a2 -> b) -> Translate c m CoreExpr b
letRecDefT ts t = letRecT (\ n -> defT (ts n) (,)) t
{-# INLINE letRecDefT #-}

-- | Rewrite all children of an expression of the form: @Let@ (@Rec@ [('Id', 'CoreExpr')]) 'CoreExpr'
letRecDefAllR :: (PathContext c, BindingContext c, Monad m) => (Int -> Rewrite c m CoreExpr) -> Rewrite c m CoreExpr -> Rewrite c m CoreExpr
letRecDefAllR rs r = letRecAllR (\ n -> defR (rs n)) r
{-# INLINE letRecDefAllR #-}

-- | Rewrite any children of an expression of the form: @Let@ (@Rec@ [('Id', 'CoreExpr')]) 'CoreExpr'
letRecDefAnyR :: (PathContext c, BindingContext c, MonadCatch m) => (Int -> Rewrite c m CoreExpr) -> Rewrite c m CoreExpr -> Rewrite c m CoreExpr
letRecDefAnyR rs r = letRecAnyR (\ n -> defR (rs n)) r
{-# INLINE letRecDefAnyR #-}

-- | Rewrite one child of an expression of the form: @Let@ (@Rec@ [('Id', 'CoreExpr')]) 'CoreExpr'
letRecDefOneR :: (PathContext c, BindingContext c, MonadCatch m) => (Int -> Rewrite c m CoreExpr) -> Rewrite c m CoreExpr -> Rewrite c m CoreExpr
letRecDefOneR rs r = letRecOneR (\ n -> defR (rs n)) r
{-# INLINE letRecDefOneR #-}


-- | Translate an expression of the form: @Case@ 'CoreExpr' 'Id' 'Type' [('AltCon', ['Var'], 'CoreExpr')]
caseAltT :: (PathContext c, BindingContext c, Monad m) => Translate c m CoreExpr a1 -> (Int -> Translate c m CoreExpr a2) -> (a1 -> Id -> Type -> [(AltCon,[Var],a2)] -> b) -> Translate c m CoreExpr b
caseAltT t ts = caseT t (\ n -> altT (ts n) (,,))
{-# INLINE caseAltT #-}

-- | Rewrite all children of an expression of the form: @Case@ 'CoreExpr' 'Id' 'Type' [('AltCon', ['Var'], 'CoreExpr')]
caseAltAllR :: (PathContext c, BindingContext c, Monad m) => Rewrite c m CoreExpr -> (Int -> Rewrite c m CoreExpr) -> Rewrite c m CoreExpr
caseAltAllR t ts = caseAllR t (\ n -> altR (ts n))
{-# INLINE caseAltAllR #-}

-- | Rewrite any children of an expression of the form: @Case@ 'CoreExpr' 'Id' 'Type' [('AltCon', ['Var'], 'CoreExpr')]
caseAltAnyR :: (PathContext c, BindingContext c, MonadCatch m) => Rewrite c m CoreExpr -> (Int -> Rewrite c m CoreExpr) -> Rewrite c m CoreExpr
caseAltAnyR t ts = caseAnyR t (\ n -> altR (ts n))
{-# INLINE caseAltAnyR #-}

-- | Rewrite one child of an expression of the form: @Case@ 'CoreExpr' 'Id' 'Type' [('AltCon', ['Var'], 'CoreExpr')]
caseAltOneR :: (PathContext c, BindingContext c, MonadCatch m) => Rewrite c m CoreExpr -> (Int -> Rewrite c m CoreExpr) -> Rewrite c m CoreExpr
caseAltOneR t ts = caseOneR t (\ n -> altR (ts n))
{-# INLINE caseAltOneR #-}

---------------------------------------------------------------------

-- | Promote a rewrite on 'ModGuts' to a rewrite on 'Core'.
promoteModGutsR :: (PathContext c, Monad m) => Rewrite c m ModGuts -> Rewrite c m Core
promoteModGutsR = promoteWithFailMsgR "This rewrite can only succeed at the module level."
{-# INLINE promoteModGutsR #-}

-- | Promote a rewrite on 'CoreProg' to a rewrite on 'Core'.
promoteProgR :: (PathContext c, Monad m) => Rewrite c m CoreProg -> Rewrite c m Core
promoteProgR = promoteWithFailMsgR "This rewrite can only succeed at program nodes (the top-level)."
{-# INLINE promoteProgR #-}

-- | Promote a rewrite on 'CoreBind' to a rewrite on 'Core'.
promoteBindR :: (PathContext c, Monad m) => Rewrite c m CoreBind -> Rewrite c m Core
promoteBindR = promoteWithFailMsgR "This rewrite can only succeed at binding group nodes."
{-# INLINE promoteBindR #-}

-- | Promote a rewrite on 'CoreDef' to a rewrite on 'Core'.
promoteDefR :: (PathContext c, Monad m) => Rewrite c m CoreDef -> Rewrite c m Core
promoteDefR = promoteWithFailMsgR "This rewrite can only succeed at recursive definition nodes."
{-# INLINE promoteDefR #-}

-- | Promote a rewrite on 'CoreAlt' to a rewrite on 'Core'.
promoteAltR :: (PathContext c, Monad m) => Rewrite c m CoreAlt -> Rewrite c m Core
promoteAltR = promoteWithFailMsgR "This rewrite can only succeed at case alternative nodes."
{-# INLINE promoteAltR #-}

-- | Promote a rewrite on 'CoreExpr' to a rewrite on 'Core'.
promoteExprR :: (PathContext c, Monad m) => Rewrite c m CoreExpr -> Rewrite c m Core
promoteExprR = promoteWithFailMsgR "This rewrite can only succeed at expression nodes."
{-# INLINE promoteExprR #-}

---------------------------------------------------------------------

-- | Promote a bidirectional rewrite on 'CoreExpr' to a bidirectional rewrite on 'Core'.
promoteExprBiR :: (PathContext c, Monad m) => BiRewrite c m CoreExpr -> BiRewrite c m Core
promoteExprBiR b = bidirectional (promoteExprR $ forewardT b) (promoteExprR $ backwardT b)
{-# INLINE promoteExprBiR #-}

---------------------------------------------------------------------

-- | Promote a translate on 'ModGuts' to a translate on 'Core'.
promoteModGutsT :: (PathContext c, Monad m) => Translate c m ModGuts b -> Translate c m Core b
promoteModGutsT = promoteWithFailMsgT "This translate can only succeed at the module level."
{-# INLINE promoteModGutsT #-}

-- | Promote a translate on 'CoreProg' to a translate on 'Core'.
promoteProgT :: (PathContext c, Monad m) => Translate c m CoreProg b -> Translate c m Core b
promoteProgT = promoteWithFailMsgT "This translate can only succeed at program nodes (the top-level)."
{-# INLINE promoteProgT #-}

-- | Promote a translate on 'CoreBind' to a translate on 'Core'.
promoteBindT :: (PathContext c, Monad m) => Translate c m CoreBind b -> Translate c m Core b
promoteBindT = promoteWithFailMsgT "This translate can only succeed at binding group nodes."
{-# INLINE promoteBindT #-}

-- | Promote a translate on 'CoreDef' to a translate on 'Core'.
promoteDefT :: (PathContext c, Monad m) => Translate c m CoreDef b -> Translate c m Core b
promoteDefT = promoteWithFailMsgT "This translate can only succeed at recursive definition nodes."
{-# INLINE promoteDefT #-}

-- | Promote a translate on 'CoreAlt' to a translate on 'Core'.
promoteAltT :: (PathContext c, Monad m) => Translate c m CoreAlt b -> Translate c m Core b
promoteAltT = promoteWithFailMsgT "This translate can only succeed at case alternative nodes."
{-# INLINE promoteAltT #-}

-- | Promote a translate on 'CoreExpr' to a translate on 'Core'.
promoteExprT :: (PathContext c, Monad m) => Translate c m CoreExpr b -> Translate c m Core b
promoteExprT = promoteWithFailMsgT "This translate can only succeed at expression nodes."
{-# INLINE promoteExprT #-}


---------------------------------------------------------------------
---------------------------------------------------------------------


-- Type Traversals

instance Walker TypeC Type where

  allR :: MonadCatch m => Rewrite TypeC m Type -> Rewrite TypeC m Type
  allR r = prefixFailMsg "allR failed: " $
           readerT $ \case
                        AppTy _ _     -> appTyAllR r r
                        FunTy _ _     -> funTyAllR r r
                        ForAllTy _ _  -> forallTyR r
                        TyConApp _ _  -> tyConAppAllR (const r)
                        _             -> idR

---------------------------------------------------------------------

-- | Translate a type of the form: @TyVarTy@ 'TyVar'
tyVarT :: Monad m => (TyVar -> b) -> Translate TypeC m Type b
tyVarT f = contextfreeT $ \case
                             TyVarTy v -> return (f v)
                             _         -> fail "not a type-variable node."
{-# INLINE tyVarT #-}


-- | Translate a type of the form: @LitTy@ 'TyLit'
litTyT :: Monad m => (TyLit -> b) -> Translate TypeC m Type b
litTyT f = contextfreeT $ \case
                           LitTy x -> return (f x)
                           _       -> fail "not a type-literal node."
{-# INLINE litTyT #-}


-- | Translate a type of the form: @AppTy@ 'Type' 'Type'
appTyT :: Monad m => Translate TypeC m Type a1 -> Translate TypeC m Type a2 -> (a1 -> a2 -> b) -> Translate TypeC m Type b
appTyT t1 t2 f = translate $ \ c -> \case
                                     AppTy ty1 ty2 -> f <$> apply t1 (c @@ 0) ty1 <*> apply t2 (c @@ 1) ty2
                                     _             -> fail "not an type-application node."
{-# INLINE appTyT #-}

-- | Rewrite all children of a type of the form: @AppTy@ 'Type' 'Type'
appTyAllR :: Monad m => Rewrite TypeC m Type -> Rewrite TypeC m Type -> Rewrite TypeC m Type
appTyAllR r1 r2 = appTyT r1 r2 AppTy
{-# INLINE appTyAllR #-}

-- | Rewrite any children of a type of the form: @AppTy@ 'Type' 'Type'
appTyAnyR :: MonadCatch m => Rewrite TypeC m Type -> Rewrite TypeC m Type -> Rewrite TypeC m Type
appTyAnyR r1 r2 = unwrapAnyR $ appTyAllR (wrapAnyR r1) (wrapAnyR r2)
{-# INLINE appTyAnyR #-}

-- | Rewrite one child of a type of the form: @AppTy@ 'Type' 'Type'
appTyOneR :: MonadCatch m => Rewrite TypeC m Type -> Rewrite TypeC m Type -> Rewrite TypeC m Type
appTyOneR r1 r2 = unwrapOneR $ appTyAllR (wrapOneR r1) (wrapOneR r2)
{-# INLINE appTyOneR #-}


-- | Translate a type of the form: @FunTy@ 'Type' 'Type'
funTyT :: Monad m => Translate TypeC m Type a1 -> Translate TypeC m Type a2 -> (a1 -> a2 -> b) -> Translate TypeC m Type b
funTyT t1 t2 f = translate $ \ c -> \case
                                     FunTy ty1 ty2 -> f <$> apply t1 (c @@ 0) ty1 <*> apply t2 (c @@ 1) ty2
                                     _             -> fail "not an type-function node."
{-# INLINE funTyT #-}

-- | Rewrite all children of a type of the form: @FunTy@ 'Type' 'Type'
funTyAllR :: Monad m => Rewrite TypeC m Type -> Rewrite TypeC m Type -> Rewrite TypeC m Type
funTyAllR r1 r2 = funTyT r1 r2 FunTy
{-# INLINE funTyAllR #-}

-- | Rewrite any children of a type of the form: @FunTy@ 'Type' 'Type'
funTyAnyR :: MonadCatch m => Rewrite TypeC m Type -> Rewrite TypeC m Type -> Rewrite TypeC m Type
funTyAnyR r1 r2 = unwrapAnyR $ funTyAllR (wrapAnyR r1) (wrapAnyR r2)
{-# INLINE funTyAnyR #-}

-- | Rewrite one child of a type of the form: @FunTy@ 'Type' 'Type'
funTyOneR :: MonadCatch m => Rewrite TypeC m Type -> Rewrite TypeC m Type -> Rewrite TypeC m Type
funTyOneR r1 r2 = unwrapOneR $ funTyAllR (wrapOneR r1) (wrapOneR r2)
{-# INLINE funTyOneR #-}


-- | Translate a type of the form: @ForAllTy@ 'TyVar' 'Type'
forallTyT :: Monad m => Translate TypeC m Type a -> (TyVar -> a -> b) -> Translate TypeC m Type b
forallTyT t f = translate $ \ c -> \case
                                      ForAllTy v ty -> f v <$> apply t (addForallTyVar v c @@ 0) ty
                                      _             -> fail "not a forall-type node."
{-# INLINE forallTyT #-}

-- | Rewrite the 'Type' body of a type of the form: @ForAllTy@ 'TyVar' 'Type'
forallTyR :: Monad m => Rewrite TypeC m Type -> Rewrite TypeC m Type
forallTyR r = forallTyT r ForAllTy
{-# INLINE forallTyR #-}


-- | Translate a type of the form: @TyConApp@ ['KindOrType']
tyConAppT :: Monad m => (Int -> Translate TypeC m KindOrType a) -> (TyCon -> [a] -> b) -> Translate TypeC m Type b
tyConAppT t f = translate $ \ c -> \case
                                      TyConApp con tys -> f con <$> sequence [ apply (t n) (c @@ n) ty | (ty,n) <- zip tys [0..] ]
                                      _                -> fail "not a type-constructor--application node."
{-# INLINE tyConAppT #-}

-- | Rewrite all children of a type of the form: @TyConApp@ ['KindOrType']
tyConAppAllR :: Monad m => (Int -> Rewrite TypeC m KindOrType) -> Rewrite TypeC m Type
tyConAppAllR rs = tyConAppT rs TyConApp
{-# INLINE tyConAppAllR #-}

-- | Rewrite any children of a type of the form: @TyConApp@ ['KindOrType']
tyConAppAnyR :: MonadCatch m => (Int -> Rewrite TypeC m KindOrType) -> Rewrite TypeC m Type
tyConAppAnyR rs = unwrapAnyR $ tyConAppAllR (wrapAnyR . rs)
{-# INLINE tyConAppAnyR #-}

-- | Rewrite one child of a type of the form: @TyConApp@ ['KindOrType']
tyConAppOneR :: MonadCatch m => (Int -> Rewrite TypeC m KindOrType) -> Rewrite TypeC m Type
tyConAppOneR rs = unwrapOneR $ tyConAppAllR (wrapOneR . rs)
{-# INLINE tyConAppOneR #-}

---------------------------------------------------------------------
