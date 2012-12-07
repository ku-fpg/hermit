{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, TupleSections, LambdaCase, InstanceSigs #-}

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
       , MultiLensH
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

import qualified Control.Category
import Control.Monad (liftM,liftM2,ap)

---------------------------------------------------------------------

type TranslateH a b = Translate HermitC HermitM a b
type RewriteH a     = Rewrite   HermitC HermitM a
type LensH a b      = Lens      HermitC HermitM a b
type MultiLensH a b = MultiLens HermitC HermitM a b

-- | A synonym for the identity rewrite.  Convienient to avoid importing Control.Category and hiding the Prelude id.
idR :: Monad m => Rewrite HermitC m a
idR = Control.Category.id
{-# INLINE idR #-}

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

instance Walker HermitC Core where

  childrenL :: MonadCatch m => MultiLens HermitC m Core Core
  childrenL = multiLens $ translate $ \ c -> \case
          ModGutsCore guts -> injectLensReturn $ apply childrenLmodguts c guts
          ProgCore p       -> injectLensReturn $ apply childrenLprog c p
          BindCore bn      -> injectLensReturn $ apply childrenLbind c bn
          DefCore def      -> injectLensReturn $ apply childrenLdef c def
          AltCore alt      -> injectLensReturn $ apply childrenLalt c alt
          ExprCore e       -> injectLensReturn $ apply childrenLexpr c e
    where
      childrenLmodguts :: MonadCatch m => Translate HermitC m ModGuts ([(HermitC,Core)] , [Core] -> m ModGuts)
      childrenLmodguts = modGutsT exposeInjectT (\ guts cp -> ([cp], \ [p] -> (\ p' -> guts {mg_binds = progToBinds p'}) <$> retractM p))
      {-# INLINE childrenLmodguts #-}

      childrenLprog :: MonadCatch m => Translate HermitC m CoreProg ([(HermitC,Core)] , [Core] -> m CoreProg)
      childrenLprog = progConsT exposeInjectT exposeInjectT (\ cbnd cp -> ([cbnd,cp], \ [bnd,p] -> ProgCons <$> retractM bnd <*> retractM p))
      {-# INLINE childrenLprog #-}

      childrenLbind :: MonadCatch m => Translate HermitC m CoreBind ([(HermitC,Core)] , [Core] -> m CoreBind)
      childrenLbind = readerT $ \case
        NonRec _ _  -> nonRecT exposeInjectT      (\ v ce  -> ([ce],  \ [e]  -> NonRec v <$> retractM e))
        Rec _       -> recT (const exposeInjectT) (\ cdefs -> (cdefs, \ defs -> defsToRecBind <$> mapM retractM defs))
      {-# INLINE childrenLbind #-}

      childrenLdef :: MonadCatch m => Translate HermitC m CoreDef ([(HermitC,Core)] , [Core] -> m CoreDef)
      childrenLdef = defT exposeInjectT (\ v ce -> ([ce], \ [e] -> Def v <$> retractM e))
      {-# INLINE childrenLdef #-}

      childrenLalt :: MonadCatch m => Translate HermitC m CoreAlt ([(HermitC,Core)] , [Core] -> m CoreAlt)
      childrenLalt = altT exposeInjectT (\ con vs ce -> ([ce], \ [e] -> (con,vs,) <$> retractM e))
      {-# INLINE childrenLalt #-}

      childrenLexpr :: MonadCatch m => Translate HermitC m CoreExpr ([(HermitC,Core)] , [Core] -> m CoreExpr)
      childrenLexpr = readerT $ \case
        Var _        -> varT                                      (\ v            -> ([],        \ []       -> return (Var v)))
        Lit _        -> litT                                      (\ x            -> ([],        \ []       -> return (Lit x)))
        App _ _      -> appT  exposeInjectT exposeInjectT         (\ ce1 ce2      -> ([ce1,ce2], \ [e1,e2]  -> App <$> retractM e1 <*> retractM e2))
        Lam _ _      -> lamT  exposeInjectT                       (\ v ce         -> ([ce],      \ [e]      -> Lam v <$> retractM e))
        Let _ _      -> letT  exposeInjectT exposeInjectT         (\ cbnd ce      -> ([cbnd,ce], \ [bnd,e]  -> Let <$> retractM bnd <*> retractM e))
        Case _ _ _ _ -> caseT exposeInjectT (const exposeInjectT) (\ ce x t calts -> (ce:calts,  \ (e:alts) -> Case <$> retractM e <*> return x <*> return t <*> mapM retractM alts))
        Cast _ _     -> castT exposeInjectT                       (\ ce co        -> ([ce],      \ [e]      -> Cast <$> retractM e <*> return co))
        Tick _ _     -> tickT exposeInjectT                       (\ t ce         -> ([ce],      \ [e]      -> Tick t <$> retractM e))
        Type _       -> typeT                                     (\ t            -> ([],        \ []       -> return (Type t)))
        Coercion _   -> coercionT                                 (\ co           -> ([],        \ []       -> return (Coercion co)))
      {-# INLINE childrenLexpr #-}

---------------------------------------------------------------------

-- | Translate a module.
--   Slightly different to the other congruence combinators: it passes in /all/ of the original to the reconstruction function.
modGutsT :: Monad m => Translate HermitC m CoreProg a -> (ModGuts -> a -> b) -> Translate HermitC m ModGuts b
modGutsT t f = translate $ \ c modGuts -> f modGuts <$> apply t (c @@ 0) (bindsToProg $ mg_binds modGuts)

-- | Rewrite the 'CoreProg' child of a module.
modGutsR :: Monad m => Rewrite HermitC m CoreProg -> Rewrite HermitC m ModGuts
modGutsR r = modGutsT r (\ modguts p -> modguts {mg_binds = progToBinds p})

---------------------------------------------------------------------

-- | Translate an empty list.
progNilT :: Monad m => b -> Translate HermitC m CoreProg b
progNilT b = contextfreeT $ \case
                               ProgNil       -> return b
                               ProgCons _ _  -> fail "not an empty program node."

progConsT' :: Monad m => Translate HermitC m CoreBind a1 -> Translate HermitC m CoreProg a2 -> (m a1 -> m a2 -> m b) -> Translate HermitC m CoreProg b
progConsT' t1 t2 f = translate $ \ c -> \case
                                           ProgCons bd p -> f (apply t1 (c @@ 0) bd) (apply t2 (addBinding bd c @@ 1) p)
                                           _             -> fail "not a non-empty program node."

-- | Translate a program of the form: ('CoreBind' @:@ 'CoreProg')
progConsT :: Monad m => Translate HermitC m CoreBind a1 -> Translate HermitC m CoreProg a2 -> (a1 -> a2 -> b) -> Translate HermitC m CoreProg b
progConsT t1 t2 f = progConsT' t1 t2 (liftM2 f)

-- | Rewrite all children of a program of the form: ('CoreBind' @:@ 'CoreProg')
progConsAllR :: Monad m => Rewrite HermitC m CoreBind -> Rewrite HermitC m CoreProg -> Rewrite HermitC m CoreProg
progConsAllR r1 r2 = progConsT r1 r2 ProgCons

-- | Rewrite any children of a program of the form: ('CoreBind' @:@ 'CoreProg')
progConsAnyR :: MonadCatch m => Rewrite HermitC m CoreBind -> Rewrite HermitC m CoreProg -> Rewrite HermitC m CoreProg
progConsAnyR r1 r2 = progConsT' (attemptR r1) (attemptR r2) (anyR_helper2 ProgCons)

-- | Rewrite one child of a program of the form: ('CoreBind' @:@ 'CoreProg')
progConsOneR :: MonadCatch m => Rewrite HermitC m CoreBind -> Rewrite HermitC m CoreProg -> Rewrite HermitC m CoreProg
progConsOneR r1 r2 = progConsT' (withArgumentT r1) (withArgumentT r2) (oneR_helper2 ProgCons)

---------------------------------------------------------------------

-- | Translate a binding group of the form: @NonRec@ 'Var' 'CoreExpr'
nonRecT :: Monad m => Translate HermitC m CoreExpr a -> (Var -> a -> b) -> Translate HermitC m CoreBind b
nonRecT t f = translate $ \ c -> \case
                                    NonRec v e -> f v <$> apply t (c @@ 0) e
                                    _          -> fail "not a non-recursive binding-group node."

-- | Rewrite the 'CoreExpr' child of a binding group of the form: @NonRec@ 'Var' 'CoreExpr'
nonRecR :: Monad m => Rewrite HermitC m CoreExpr -> Rewrite HermitC m CoreBind
nonRecR r = nonRecT r NonRec

recT' :: Monad m => (Int -> Translate HermitC m CoreDef a) -> ([m a] -> m b) -> Translate HermitC m CoreBind b
recT' t f = translate $ \ c -> \case
         Rec bds -> -- Notice how we add the scoping bindings here *before* descending into each individual definition.
                    let c' = addBinding (Rec bds) c
                     in f [ apply (t n) (c' @@ n) (Def v e) -- here we convert from (Id,CoreExpr) to CoreDef
                          | ((v,e),n) <- zip bds [0..]
                          ]
         _       -> fail "not a recursive binding-group node."

-- | Translate a binding group of the form: @Rec@ ['CoreDef']
recT :: Monad m => (Int -> Translate HermitC m CoreDef a) -> ([a] -> b) -> Translate HermitC m CoreBind b
recT ts f = recT' ts (liftM f . sequence)

-- | Rewrite all children of a binding group of the form: @Rec@ ['CoreDef']
recAllR :: Monad m => (Int -> Rewrite HermitC m CoreDef) -> Rewrite HermitC m CoreBind
recAllR rs = recT rs defsToRecBind

-- | Rewrite any children of a binding group of the form: @Rec@ ['CoreDef']
recAnyR :: MonadCatch m => (Int -> Rewrite HermitC m CoreDef) -> Rewrite HermitC m CoreBind
recAnyR rs = recT' (attemptR . rs) (anyR_helper defsToRecBind)

-- | Rewrite one child of a binding group of the form: @Rec@ ['CoreDef']
recOneR :: MonadCatch m => (Int -> Rewrite HermitC m CoreDef) -> Rewrite HermitC m CoreBind
recOneR rs = recT' (withArgumentT . rs) (oneR_helper defsToRecBind)

---------------------------------------------------------------------

-- | Translate a recursive definition of the form: @Def@ 'Id' 'CoreExpr'
defT :: Monad m => Translate HermitC m CoreExpr a -> (Id -> a -> b) -> Translate HermitC m CoreDef b
defT t f = translate $ \ c (Def v e) -> f v <$> apply t (c @@ 0) e

-- | Rewrite the 'CoreExpr' child of a recursive definition of the form: @Def@ 'Id' 'CoreExpr'
defR :: Monad m => Rewrite HermitC m CoreExpr -> Rewrite HermitC m CoreDef
defR r = defT r Def

---------------------------------------------------------------------

-- | Translate a case alternative of the form: ('AltCon', ['Id'], 'CoreExpr')
altT :: Monad m => Translate HermitC m CoreExpr a -> (AltCon -> [Id] -> a -> b) -> Translate HermitC m CoreAlt b
altT t f = translate $ \ c (con,bs,e) -> f con bs <$> apply t (addAltBindings bs c @@ 0) e

-- | Rewrite the 'CoreExpr' child of a case alternative of the form: ('AltCon', 'Id', 'CoreExpr')
altR :: Monad m => Rewrite HermitC m CoreExpr -> Rewrite HermitC m CoreAlt
altR r = altT r (,,)

---------------------------------------------------------------------

-- | Translate an expression of the form: @Var@ 'Var'
varT :: Monad m => (Var -> b) -> Translate HermitC m CoreExpr b
varT f = contextfreeT $ \case
                           Var v -> return (f v)
                           _     -> fail "not a variable node."

-- | Translate an expression of the form: @Lit@ 'Literal'
litT :: Monad m => (Literal -> b) -> Translate HermitC m CoreExpr b
litT f = contextfreeT $ \case
                           Lit x -> return (f x)
                           _     -> fail "not a literal node."


appT' :: Monad m => Translate HermitC m CoreExpr a1 -> Translate HermitC m CoreExpr a2 -> (m a1 -> m a2 -> m b) -> Translate HermitC m CoreExpr b
appT' t1 t2 f = translate $ \ c -> \case
                                      App e1 e2 -> f (apply t1 (c @@ 0) e1) (apply t2 (c @@ 1) e2)
                                      _         -> fail "not an application node."

-- | Translate an expression of the form: @App@ 'CoreExpr' 'CoreExpr'
appT :: Monad m => Translate HermitC m CoreExpr a1 -> Translate HermitC m CoreExpr a2 -> (a1 -> a2 -> b) -> Translate HermitC m CoreExpr b
appT t1 t2 = appT' t1 t2 . liftM2

-- | Rewrite all children of an expression of the form: @App@ 'CoreExpr' 'CoreExpr'
appAllR :: Monad m => Rewrite HermitC m CoreExpr -> Rewrite HermitC m CoreExpr -> Rewrite HermitC m CoreExpr
appAllR r1 r2 = appT r1 r2 App

-- | Rewrite any children of an expression of the form: @App@ 'CoreExpr' 'CoreExpr'
appAnyR :: MonadCatch m => Rewrite HermitC m CoreExpr -> Rewrite HermitC m CoreExpr -> Rewrite HermitC m CoreExpr
appAnyR r1 r2 = appT' (attemptR r1) (attemptR r2) (anyR_helper2 App)

-- | Rewrite one child of an expression of the form: @App@ 'CoreExpr' 'CoreExpr'
appOneR :: MonadCatch m => Rewrite HermitC m CoreExpr -> Rewrite HermitC m CoreExpr -> Rewrite HermitC m CoreExpr
appOneR r1 r2 = appT' (withArgumentT r1) (withArgumentT r2) (oneR_helper2 App)


-- | Translate an expression of the form: @Lam@ 'Var' 'CoreExpr'
lamT :: Monad m => Translate HermitC m CoreExpr a -> (Var -> a -> b) -> Translate HermitC m CoreExpr b
lamT t f = translate $ \ c -> \case
                                 Lam b e -> f b <$> apply t (addLambdaBinding b c @@ 0) e
                                 _       -> fail "not a lambda node."

-- | Rewrite the 'CoreExpr' child of an expression of the form: @Lam@ 'Var' 'CoreExpr'
lamR :: Monad m => Rewrite HermitC m CoreExpr -> Rewrite HermitC m CoreExpr
lamR r = lamT r Lam


letT' :: Monad m => Translate HermitC m CoreBind a1 -> Translate HermitC m CoreExpr a2 -> (m a1 -> m a2 -> m b) -> Translate HermitC m CoreExpr b
letT' t1 t2 f = translate $ \ c -> \case
        Let bds e -> -- Note we use the *original* context for the binding group.
                     -- If the bindings are recursive, they will be added to the context by recT'.
                     f (apply t1 (c @@ 0) bds) (apply t2 (addBinding bds c @@ 1) e)
        _         -> fail "not a let node."

-- | Translate an expression of the form: @Let@ 'CoreBind' 'CoreExpr'
letT :: Monad m => Translate HermitC m CoreBind a1 -> Translate HermitC m CoreExpr a2 -> (a1 -> a2 -> b) -> Translate HermitC m CoreExpr b
letT t1 t2 = letT' t1 t2 . liftM2

-- | Rewrite all children of an expression of the form: @Let@ 'CoreBind' 'CoreExpr'
letAllR :: Monad m => Rewrite HermitC m CoreBind -> Rewrite HermitC m CoreExpr -> Rewrite HermitC m CoreExpr
letAllR r1 r2 = letT r1 r2 Let

-- | Rewrite any children of an expression of the form: @Let@ 'CoreBind' 'CoreExpr'
letAnyR :: MonadCatch m => Rewrite HermitC m CoreBind -> Rewrite HermitC m CoreExpr -> Rewrite HermitC m CoreExpr
letAnyR r1 r2 = letT' (attemptR r1) (attemptR r2) (anyR_helper2 Let)

-- | Rewrite one child of an expression of the form: @Let@ 'CoreBind' 'CoreExpr'
letOneR :: MonadCatch m => Rewrite HermitC m CoreBind -> Rewrite HermitC m CoreExpr -> Rewrite HermitC m CoreExpr
letOneR r1 r2 = letT' (withArgumentT r1) (withArgumentT r2) (oneR_helper2 Let)


caseT' :: Monad m => Translate HermitC m CoreExpr a1 -> (Int -> Translate HermitC m CoreAlt a2) -> (Id -> Type -> m a1 -> [m a2] -> m b) -> Translate HermitC m CoreExpr b
caseT' t ts f = translate $ \ c -> \case
         Case e b ty alts -> f b ty (apply t (c @@ 0) e) $ [ apply (ts n) (addCaseBinding (b,e,alt) c @@ (n+1)) alt
                                                           | (alt,n) <- zip alts [0..]
                                                           ]
         _                -> fail "not a case node."

-- | Translate an expression of the form: @Case@ 'CoreExpr' 'Id' 'Type' ['CoreAlt']
caseT :: Monad m => Translate HermitC m CoreExpr a1 -> (Int -> Translate HermitC m CoreAlt a2) -> (a1 -> Id -> Type -> [a2] -> b) -> Translate HermitC m CoreExpr b
caseT t ts f = caseT' t ts (\ b ty me malts -> f <$> me <*> return b <*> return ty <*> sequence malts)

-- | Rewrite all children of an expression of the form: @Case@ 'CoreExpr' 'Id' 'Type' ['CoreAlt']
caseAllR :: Monad m => Rewrite HermitC m CoreExpr -> (Int -> Rewrite HermitC m CoreAlt) -> Rewrite HermitC m CoreExpr
caseAllR r rs = caseT r rs Case

-- | Rewrite any children of an expression of the form: @Case@ 'CoreExpr' 'Id' 'Type' ['CoreAlt']
caseAnyR :: MonadCatch m => Rewrite HermitC m CoreExpr -> (Int -> Rewrite HermitC m CoreAlt) -> Rewrite HermitC m CoreExpr
caseAnyR r rs = caseT' (attemptR r) (attemptR . rs) (\ b ty -> anyR_helper1N (\ e -> Case e b ty))

-- | Rewrite one child of an expression of the form: @Case@ 'CoreExpr' 'Id' 'Type' ['CoreAlt']
caseOneR :: MonadCatch m => Rewrite HermitC m CoreExpr -> (Int -> Rewrite HermitC m CoreAlt) -> Rewrite HermitC m CoreExpr
caseOneR r rs = caseT' (withArgumentT r) (withArgumentT . rs) (\ b ty -> oneR_helper1N (\ e -> Case e b ty))

-- | Translate an expression of the form: @Cast@ 'CoreExpr' 'Coercion'
castT :: Monad m => Translate HermitC m CoreExpr a -> (a -> Coercion -> b) -> Translate HermitC m CoreExpr b
castT t f = translate $ \ c -> \case
                                  Cast e cast -> f <$> apply t (c @@ 0) e <*> return cast
                                  _           -> fail "not a cast node."

-- | Rewrite the 'CoreExpr' child of an expression of the form: @Cast@ 'CoreExpr' 'Coercion'
castR :: Monad m => Rewrite HermitC m CoreExpr -> Rewrite HermitC m CoreExpr
castR r = castT r Cast

-- | Translate an expression of the form: @Tick@ 'CoreTickish' 'CoreExpr'
tickT :: Monad m => Translate HermitC m CoreExpr a -> (CoreTickish -> a -> b) -> Translate HermitC m CoreExpr b
tickT t f = translate $ \ c -> \case
        Tick tk e -> f tk <$> apply t (c @@ 0) e
        _         -> fail "not a tick node."

-- | Rewrite the 'CoreExpr' child of an expression of the form: @Tick@ 'CoreTickish' 'CoreExpr'
tickR :: Monad m => Rewrite HermitC m CoreExpr -> Rewrite HermitC m CoreExpr
tickR r = tickT r Tick

-- | Translate an expression of the form: @Type@ 'Type'
typeT :: Monad m => (Type -> b) -> Translate HermitC m CoreExpr b
typeT f = contextfreeT $ \case
                            Type t -> return (f t)
                            _      -> fail "not a type node."

-- | Translate an expression of the form: @Coercion@ 'Coercion'
coercionT :: Monad m => (Coercion -> b) -> Translate HermitC m CoreExpr b
coercionT f = contextfreeT $ \case
                                Coercion co -> return (f co)
                                _           -> fail "not a coercion node."

---------------------------------------------------------------------

-- Some composite congruence combinators to export.

-- | Translate a binding group of the form: @Rec@ [('Id', 'CoreExpr')]
recDefT :: Monad m => (Int -> Translate HermitC m CoreExpr a1) -> ([(Id,a1)] -> b) -> Translate HermitC m CoreBind b
recDefT ts = recT (\ n -> defT (ts n) (,))

-- | Rewrite all children of a binding group of the form: @Rec@ [('Id', 'CoreExpr')]
recDefAllR :: Monad m => (Int -> Rewrite HermitC m CoreExpr) -> Rewrite HermitC m CoreBind
recDefAllR rs = recAllR (\ n -> defR (rs n))

-- | Rewrite any children of a binding group of the form: @Rec@ [('Id', 'CoreExpr')]
recDefAnyR :: MonadCatch m => (Int -> Rewrite HermitC m CoreExpr) -> Rewrite HermitC m CoreBind
recDefAnyR rs = recAnyR (\ n -> defR (rs n))

-- | Rewrite one child of a binding group of the form: @Rec@ [('Id', 'CoreExpr')]
recDefOneR :: MonadCatch m => (Int -> Rewrite HermitC m CoreExpr) -> Rewrite HermitC m CoreBind
recDefOneR rs = recOneR (\ n -> defR (rs n))


-- | Translate a program of the form: (@NonRec@ 'Var' 'CoreExpr') @:@ 'CoreProg'
consNonRecT :: Monad m => Translate HermitC m CoreExpr a1 -> Translate HermitC m CoreProg a2 -> (Var -> a1 -> a2 -> b) -> Translate HermitC m CoreProg b
consNonRecT t1 t2 f = progConsT (nonRecT t1 (,)) t2 (uncurry f)

-- | Rewrite all children of an expression of the form: (@NonRec@ 'Var' 'CoreExpr') @:@ 'CoreProg'
consNonRecAllR :: Monad m => Rewrite HermitC m CoreExpr -> Rewrite HermitC m CoreProg -> Rewrite HermitC m CoreProg
consNonRecAllR r1 r2 = progConsAllR (nonRecR r1) r2

-- | Rewrite any children of an expression of the form: (@NonRec@ 'Var' 'CoreExpr') @:@ 'CoreProg'
consNonRecAnyR :: MonadCatch m => Rewrite HermitC m CoreExpr -> Rewrite HermitC m CoreProg -> Rewrite HermitC m CoreProg
consNonRecAnyR r1 r2 = progConsAnyR (nonRecR r1) r2

-- | Rewrite one child of an expression of the form: (@NonRec@ 'Var' 'CoreExpr') @:@ 'CoreProg'
consNonRecOneR :: MonadCatch m => Rewrite HermitC m CoreExpr -> Rewrite HermitC m CoreProg -> Rewrite HermitC m CoreProg
consNonRecOneR r1 r2 = progConsOneR (nonRecR r1) r2


-- | Translate an expression of the form: (@Rec@ ['CoreDef']) @:@ 'CoreProg'
consRecT :: Monad m => (Int -> Translate HermitC m CoreDef a1) -> Translate HermitC m CoreProg a2 -> ([a1] -> a2 -> b) -> Translate HermitC m CoreProg b
consRecT ts t = progConsT (recT ts id) t

-- | Rewrite all children of an expression of the form: (@Rec@ ['CoreDef']) @:@ 'CoreProg'
consRecAllR :: Monad m => (Int -> Rewrite HermitC m CoreDef) -> Rewrite HermitC m CoreProg -> Rewrite HermitC m CoreProg
consRecAllR rs r = progConsAllR (recAllR rs) r

-- | Rewrite any children of an expression of the form: (@Rec@ ['CoreDef']) @:@ 'CoreProg'
consRecAnyR :: MonadCatch m => (Int -> Rewrite HermitC m CoreDef) -> Rewrite HermitC m CoreProg -> Rewrite HermitC m CoreProg
consRecAnyR rs r = progConsAnyR (recAnyR rs) r

-- | Rewrite one child of an expression of the form: (@Rec@ ['CoreDef']) @:@ 'CoreProg'
consRecOneR :: MonadCatch m => (Int -> Rewrite HermitC m CoreDef) -> Rewrite HermitC m CoreProg -> Rewrite HermitC m CoreProg
consRecOneR rs r = progConsOneR (recOneR rs) r


-- | Translate an expression of the form: (@Rec@ [('Id', 'CoreExpr')]) @:@ 'CoreProg'
consRecDefT :: Monad m => (Int -> Translate HermitC m CoreExpr a1) -> Translate HermitC m CoreProg a2 -> ([(Id,a1)] -> a2 -> b) -> Translate HermitC m CoreProg b
consRecDefT ts t = consRecT (\ n -> defT (ts n) (,)) t

-- | Rewrite all children of an expression of the form: (@Rec@ [('Id', 'CoreExpr')]) @:@ 'CoreProg'
consRecDefAllR :: Monad m => (Int -> Rewrite HermitC m CoreExpr) -> Rewrite HermitC m CoreProg -> Rewrite HermitC m CoreProg
consRecDefAllR rs r = consRecAllR (\ n -> defR (rs n)) r

-- | Rewrite any children of an expression of the form: (@Rec@ [('Id', 'CoreExpr')]) @:@ 'CoreProg'
consRecDefAnyR :: MonadCatch m => (Int -> Rewrite HermitC m CoreExpr) -> Rewrite HermitC m CoreProg -> Rewrite HermitC m CoreProg
consRecDefAnyR rs r = consRecAnyR (\ n -> defR (rs n)) r

-- | Rewrite one child of an expression of the form: (@Rec@ [('Id', 'CoreExpr')]) @:@ 'CoreProg'
consRecDefOneR :: MonadCatch m => (Int -> Rewrite HermitC m CoreExpr) -> Rewrite HermitC m CoreProg -> Rewrite HermitC m CoreProg
consRecDefOneR rs r = consRecOneR (\ n -> defR (rs n)) r


-- | Translate an expression of the form: @Let@ (@NonRec@ 'Var' 'CoreExpr') 'CoreExpr'
letNonRecT :: Monad m => Translate HermitC m CoreExpr a1 -> Translate HermitC m CoreExpr a2 -> (Var -> a1 -> a2 -> b) -> Translate HermitC m CoreExpr b
letNonRecT t1 t2 f = letT (nonRecT t1 (,)) t2 (uncurry f)

-- | Rewrite all children of an expression of the form: @Let@ (@NonRec@ 'Var' 'CoreExpr') 'CoreExpr'
letNonRecAllR :: Monad m => Rewrite HermitC m CoreExpr -> Rewrite HermitC m CoreExpr -> Rewrite HermitC m CoreExpr
letNonRecAllR r1 r2 = letAllR (nonRecR r1) r2

-- | Rewrite any children of an expression of the form: @Let@ (@NonRec@ 'Var' 'CoreExpr') 'CoreExpr'
letNonRecAnyR :: MonadCatch m => Rewrite HermitC m CoreExpr -> Rewrite HermitC m CoreExpr -> Rewrite HermitC m CoreExpr
letNonRecAnyR r1 r2 = letAnyR (nonRecR r1) r2

-- | Rewrite one child of an expression of the form: @Let@ (@NonRec@ 'Var' 'CoreExpr') 'CoreExpr'
letNonRecOneR :: MonadCatch m => Rewrite HermitC m CoreExpr -> Rewrite HermitC m CoreExpr -> Rewrite HermitC m CoreExpr
letNonRecOneR r1 r2 = letOneR (nonRecR r1) r2


-- | Translate an expression of the form: @Let@ (@Rec@ ['CoreDef']) 'CoreExpr'
letRecT :: Monad m => (Int -> Translate HermitC m CoreDef a1) -> Translate HermitC m CoreExpr a2 -> ([a1] -> a2 -> b) -> Translate HermitC m CoreExpr b
letRecT ts t = letT (recT ts id) t

-- | Rewrite all children of an expression of the form: @Let@ (@Rec@ ['CoreDef']) 'CoreExpr'
letRecAllR :: Monad m => (Int -> Rewrite HermitC m CoreDef) -> Rewrite HermitC m CoreExpr -> Rewrite HermitC m CoreExpr
letRecAllR rs r = letAllR (recAllR rs) r

-- | Rewrite any children of an expression of the form: @Let@ (@Rec@ ['CoreDef']) 'CoreExpr'
letRecAnyR :: MonadCatch m => (Int -> Rewrite HermitC m CoreDef) -> Rewrite HermitC m CoreExpr -> Rewrite HermitC m CoreExpr
letRecAnyR rs r = letAnyR (recAnyR rs) r

-- | Rewrite one child of an expression of the form: @Let@ (@Rec@ ['CoreDef']) 'CoreExpr'
letRecOneR :: MonadCatch m => (Int -> Rewrite HermitC m CoreDef) -> Rewrite HermitC m CoreExpr -> Rewrite HermitC m CoreExpr
letRecOneR rs r = letOneR (recOneR rs) r


-- | Translate an expression of the form: @Let@ (@Rec@ [('Id', 'CoreExpr')]) 'CoreExpr'
letRecDefT :: Monad m => (Int -> Translate HermitC m CoreExpr a1) -> Translate HermitC m CoreExpr a2 -> ([(Id,a1)] -> a2 -> b) -> Translate HermitC m CoreExpr b
letRecDefT ts t = letRecT (\ n -> defT (ts n) (,)) t

-- | Rewrite all children of an expression of the form: @Let@ (@Rec@ [('Id', 'CoreExpr')]) 'CoreExpr'
letRecDefAllR :: Monad m => (Int -> Rewrite HermitC m CoreExpr) -> Rewrite HermitC m CoreExpr -> Rewrite HermitC m CoreExpr
letRecDefAllR rs r = letRecAllR (\ n -> defR (rs n)) r

-- | Rewrite any children of an expression of the form: @Let@ (@Rec@ [('Id', 'CoreExpr')]) 'CoreExpr'
letRecDefAnyR :: MonadCatch m => (Int -> Rewrite HermitC m CoreExpr) -> Rewrite HermitC m CoreExpr -> Rewrite HermitC m CoreExpr
letRecDefAnyR rs r = letRecAnyR (\ n -> defR (rs n)) r

-- | Rewrite one child of an expression of the form: @Let@ (@Rec@ [('Id', 'CoreExpr')]) 'CoreExpr'
letRecDefOneR :: MonadCatch m => (Int -> Rewrite HermitC m CoreExpr) -> Rewrite HermitC m CoreExpr -> Rewrite HermitC m CoreExpr
letRecDefOneR rs r = letRecOneR (\ n -> defR (rs n)) r


-- | Translate an expression of the form: @Case@ 'CoreExpr' 'Id' 'Type' [('AltCon', ['Id'], 'CoreExpr')]
caseAltT :: Monad m => Translate HermitC m CoreExpr a1 -> (Int -> Translate HermitC m CoreExpr a2) -> (a1 -> Id -> Type -> [(AltCon,[Id],a2)] -> b) -> Translate HermitC m CoreExpr b
caseAltT t ts = caseT t (\ n -> altT (ts n) (,,))

-- | Rewrite all children of an expression of the form: @Case@ 'CoreExpr' 'Id' 'Type' [('AltCon', ['Id'], 'CoreExpr')]
caseAltAllR :: Monad m => Rewrite HermitC m CoreExpr -> (Int -> Rewrite HermitC m CoreExpr) -> Rewrite HermitC m CoreExpr
caseAltAllR t ts = caseAllR t (\ n -> altR (ts n))

-- | Rewrite any children of an expression of the form: @Case@ 'CoreExpr' 'Id' 'Type' [('AltCon', ['Id'], 'CoreExpr')]
caseAltAnyR :: MonadCatch m => Rewrite HermitC m CoreExpr -> (Int -> Rewrite HermitC m CoreExpr) -> Rewrite HermitC m CoreExpr
caseAltAnyR t ts = caseAnyR t (\ n -> altR (ts n))

-- | Rewrite one child of an expression of the form: @Case@ 'CoreExpr' 'Id' 'Type' [('AltCon', ['Id'], 'CoreExpr')]
caseAltOneR :: MonadCatch m => Rewrite HermitC m CoreExpr -> (Int -> Rewrite HermitC m CoreExpr) -> Rewrite HermitC m CoreExpr
caseAltOneR t ts = caseOneR t (\ n -> altR (ts n))

---------------------------------------------------------------------

-- | Promote a rewrite on 'ModGuts' to a rewrite on 'Core'.
promoteModGutsR :: Monad m => Rewrite HermitC m ModGuts -> Rewrite HermitC m Core
promoteModGutsR = promoteWithFailMsgR "This rewrite can only succeed at the module level."

-- | Promote a rewrite on 'CoreProg' to a rewrite on 'Core'.
promoteProgR :: Monad m => Rewrite HermitC m CoreProg -> Rewrite HermitC m Core
promoteProgR = promoteWithFailMsgR "This rewrite can only succeed at program nodes (the top-level)."

-- | Promote a rewrite on 'CoreBind' to a rewrite on 'Core'.
promoteBindR :: Monad m => Rewrite HermitC m CoreBind -> Rewrite HermitC m Core
promoteBindR = promoteWithFailMsgR "This rewrite can only succeed at binding group nodes."

-- | Promote a rewrite on 'CoreDef' to a rewrite on 'Core'.
promoteDefR :: Monad m => Rewrite HermitC m CoreDef -> Rewrite HermitC m Core
promoteDefR = promoteWithFailMsgR "This rewrite can only succeed at recursive definition nodes."

-- | Promote a rewrite on 'CoreAlt' to a rewrite on 'Core'.
promoteAltR :: Monad m => Rewrite HermitC m CoreAlt -> Rewrite HermitC m Core
promoteAltR = promoteWithFailMsgR "This rewrite can only succeed at case alternative nodes."

-- | Promote a rewrite on 'CoreExpr' to a rewrite on 'Core'.
promoteExprR :: Monad m => Rewrite HermitC m CoreExpr -> Rewrite HermitC m Core
promoteExprR = promoteWithFailMsgR "This rewrite can only succeed at expression nodes."

---------------------------------------------------------------------

-- | Promote a translate on 'ModGuts' to a translate on 'Core'.
promoteModGutsT :: Monad m => Translate HermitC m ModGuts b -> Translate HermitC m Core b
promoteModGutsT = promoteWithFailMsgT "This translate can only succeed at the module level."

-- | Promote a translate on 'CoreProg' to a translate on 'Core'.
promoteProgT :: Monad m => Translate HermitC m CoreProg b -> Translate HermitC m Core b
promoteProgT = promoteWithFailMsgT "This translate can only succeed at program nodes (the top-level)."

-- | Promote a translate on 'CoreBind' to a translate on 'Core'.
promoteBindT :: Monad m => Translate HermitC m CoreBind b -> Translate HermitC m Core b
promoteBindT = promoteWithFailMsgT "This translate can only succeed at binding group nodes."

-- | Promote a translate on 'CoreDef' to a translate on 'Core'.
promoteDefT :: Monad m => Translate HermitC m CoreDef b -> Translate HermitC m Core b
promoteDefT = promoteWithFailMsgT "This translate can only succeed at recursive definition nodes."

-- | Promote a translate on 'CoreAlt' to a translate on 'Core'.
promoteAltT :: Monad m => Translate HermitC m CoreAlt b -> Translate HermitC m Core b
promoteAltT = promoteWithFailMsgT "This translate can only succeed at case alternative nodes."

-- | Promote a translate on 'CoreExpr' to a translate on 'Core'.
promoteExprT :: Monad m => Translate HermitC m CoreExpr b -> Translate HermitC m Core b
promoteExprT = promoteWithFailMsgT "This translate can only succeed at expression nodes."

---------------------------------------------------------------------
