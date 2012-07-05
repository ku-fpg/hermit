{-# LANGUAGE MultiParamTypeClasses, TypeFamilies, FlexibleInstances, FlexibleContexts, TupleSections #-}

module Language.HERMIT.Kure
       (
       -- * KURE Modules

       -- | All the required functionality of KURE is exported here, so other modules do not need to import KURE directly.
         module Language.KURE
       , module Language.KURE.Injection
       -- * Synonyms

       -- | In HERMIT, 'Translate', 'Rewrite' and 'Lens' always operate the same context and monad.
       , TranslateH
       , RewriteH
       , LensH
       , idR
       -- * Generic Data Type
       -- $typenote
       , Core(..), CoreDef(..)
       -- * Congruence combinators
       -- ** Modguts
       , modGutsT, modGutsR
       -- ** Program
       , nilT
       , consBindT, consBindAllR, consBindAnyR, consBindOneR
       -- ** Bindings
       , nonRecT, nonRecR
       , recT, recAllR, recAnyR, recOneR
       -- ** Recursive Definitions
       , defT, defR
       -- ** Alternatives
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
       , letNonRecT, letNonRecAllR, letNonRecAnyR, letNonRecOneR
       , letRecT, letRecAllR, letRecAnyR, letRecOneR
       , recDefT, recDefAllR, recDefAnyR, recDefOneR
       , letRecDefT, letRecDefAllR, letRecDefAnyR, letRecDefOneR
       )
where

import GhcPlugins hiding (empty)

import Language.KURE
import Language.KURE.Injection
import Language.KURE.Utilities

import Language.HERMIT.Context
import Language.HERMIT.Monad

import Control.Applicative
import qualified Control.Category
import Control.Arrow

import Data.Monoid

---------------------------------------------------------------------

type TranslateH a b = Translate Context HermitM a b
type RewriteH a = Rewrite Context HermitM a
type LensH a b = Lens Context HermitM a b

-- | A synonym for the identity rewrite.  Convienient to avoid importing Control.Category.
idR :: RewriteH a
idR = Control.Category.id

---------------------------------------------------------------------

-- $typenote
--   NOTE: 'Type' is not included in the generic datatype.
--   However, we could have included it and provided the facility for descending into types.
--   We have not done so because
--     (a) we do not need that functionality, and
--     (b) the types are complicated and we're not sure that we understand them.

-- | In GHC Core, recursive definitions are encoded as (Id, CoreExpr) pairs.
--   Here we use an isomorphic data type.
data CoreDef = Def Id CoreExpr

defToRecBind :: [CoreDef] -> CoreBind
defToRecBind = Rec . map (\ (Def v e) -> (v,e))

-- | Core is the sum type of all nodes in the AST that we wish to be able to traverse.
--   All 'Node' instances define 'Core' to be the 'Generic' type.
data Core = ModGutsCore  ModGuts
          | ProgramCore  CoreProgram
          | BindCore     CoreBind
          | DefCore      CoreDef
          | ExprCore     CoreExpr
          | AltCore      CoreAlt

---------------------------------------------------------------------

instance Node Core where
  type Generic Core = Core

  numChildren (ModGutsCore x) = numChildren x
  numChildren (ProgramCore x) = numChildren x
  numChildren (BindCore x)    = numChildren x
  numChildren (DefCore x)     = numChildren x
  numChildren (ExprCore x)    = numChildren x
  numChildren (AltCore x)     = numChildren x

-- Defining Walker instances for the Generic type 'Core' is almost entirely automated by KURE.
-- Unfortunately, you still need to pattern match on the 'Core' data type.

instance Walker Context HermitM Core where
  childL n = lens $ translate $ \ c core -> case core of
          ModGutsCore x -> childLgeneric n c x
          ProgramCore x -> childLgeneric n c x
          BindCore x    -> childLgeneric n c x
          DefCore x     -> childLgeneric n c x
          ExprCore x    -> childLgeneric n c x
          AltCore x     -> childLgeneric n c x

  allT t = translate $ \ c core -> case core of
          ModGutsCore x -> allTgeneric t c x
          ProgramCore x -> allTgeneric t c x
          BindCore x    -> allTgeneric t c x
          DefCore x     -> allTgeneric t c x
          ExprCore x    -> allTgeneric t c x
          AltCore x     -> allTgeneric t c x

  oneT t = translate $ \ c core -> case core of
          ModGutsCore x -> oneTgeneric t c x
          ProgramCore x -> oneTgeneric t c x
          BindCore x    -> oneTgeneric t c x
          DefCore x     -> oneTgeneric t c x
          ExprCore x    -> oneTgeneric t c x
          AltCore x     -> oneTgeneric t c x

  allR r = rewrite $ \ c core -> case core of
          ModGutsCore x -> allRgeneric r c x
          ProgramCore x -> allRgeneric r c x
          BindCore x    -> allRgeneric r c x
          DefCore x     -> allRgeneric r c x
          ExprCore x    -> allRgeneric r c x
          AltCore x     -> allRgeneric r c x

  anyR r = rewrite $ \ c core -> case core of
          ModGutsCore x -> anyRgeneric r c x
          ProgramCore x -> anyRgeneric r c x
          BindCore x    -> anyRgeneric r c x
          DefCore x     -> anyRgeneric r c x
          ExprCore x    -> anyRgeneric r c x
          AltCore x     -> anyRgeneric r c x

  oneR r = rewrite $ \ c core -> case core of
          ModGutsCore x -> oneRgeneric r c x
          ProgramCore x -> oneRgeneric r c x
          BindCore x    -> oneRgeneric r c x
          DefCore x     -> oneRgeneric r c x
          ExprCore x    -> oneRgeneric r c x
          AltCore x     -> oneRgeneric r c x

---------------------------------------------------------------------

instance Injection ModGuts Core where
  inject                     = ModGutsCore
  retract (ModGutsCore guts) = Just guts
  retract _                  = Nothing

instance Node ModGuts where
  type Generic ModGuts = Core

  numChildren _ = 1

instance Walker Context HermitM ModGuts where
  childL 0 = lens $ modGutsT exposeT (childL1of2 $ \ modguts bds -> modguts {mg_binds = bds})
  childL n = failT (missingChild n)

-- | Slightly different to the others; passes in *all* of the original to the reconstruction function.
modGutsT :: TranslateH CoreProgram a -> (ModGuts -> a -> b) -> TranslateH ModGuts b
modGutsT t f = translate $ \ c modGuts -> f modGuts <$> apply t (c @@ 0) (mg_binds modGuts)

modGutsR :: RewriteH CoreProgram -> RewriteH ModGuts
modGutsR r = modGutsT r (\ modguts bds -> modguts {mg_binds = bds})

---------------------------------------------------------------------

instance Injection CoreProgram Core where
  inject                    = ProgramCore
  retract (ProgramCore bds) = Just bds
  retract _                 = Nothing

instance Node CoreProgram where
  type Generic CoreProgram = Core

  -- we consider only the head and tail to be interesting children
  numChildren bds = min 2 (length bds)

instance Walker Context HermitM CoreProgram where
  childL 0 = lens $ consBindT exposeT idR (childL0of2 (:))
  childL 1 = lens $ consBindT idR exposeT (childL1of2 (:))
  childL n = failT (missingChild n)

nilT :: b -> TranslateH [a] b
nilT b = contextfreeT $ \ e -> case e of
                           [] -> pure b
                           _  -> fail "no match for []"

consBindT' :: TranslateH CoreBind a1 -> TranslateH [CoreBind] a2 -> (HermitM a1 -> HermitM a2 -> HermitM b) -> TranslateH [CoreBind] b
consBindT' t1 t2 f = translate $ \ c e -> case e of
        bd:bds -> f (apply t1 (c @@ 0) bd) (apply t2 (addBinding bd c @@ 1) bds)
        _      -> fail "no match for consBind"

consBindT :: TranslateH CoreBind a1 -> TranslateH [CoreBind] a2 -> (a1 -> a2 -> b) -> TranslateH [CoreBind] b
consBindT t1 t2 f = consBindT' t1 t2 (liftA2 f)

consBindAllR :: RewriteH CoreBind -> RewriteH [CoreBind] -> RewriteH [CoreBind]
consBindAllR r1 r2 = consBindT r1 r2 (:)

consBindAnyR :: RewriteH CoreBind -> RewriteH [CoreBind] -> RewriteH [CoreBind]
consBindAnyR r1 r2 = consBindT' (attemptR r1) (attemptR r2) (attemptAny2 (:))

consBindOneR :: RewriteH CoreBind -> RewriteH [CoreBind] -> RewriteH [CoreBind]
consBindOneR r1 r2 = consBindT' (withArgumentT r1) (withArgumentT r2) (attemptOne2 (:))

---------------------------------------------------------------------

instance Injection CoreBind Core where
  inject                  = BindCore
  retract (BindCore bnd)  = Just bnd
  retract _               = Nothing

instance Node CoreBind where
  type Generic CoreBind = Core

  numChildren (NonRec _ _) = 1
  numChildren (Rec defs)   = length defs

instance Walker Context HermitM CoreBind where
  childL n = lens $ setFailMsg (missingChild n) $
               case n of
                 0 -> nonrec <+ rec
                 _ -> rec

    where
      nonrec = nonRecT exposeT (childL1of2 NonRec)
      rec    = whenM (arr $ hasChild n) $
                  recT (const exposeT) (childLMofN n defToRecBind)

  allT t = nonRecT (extractT t) (\ _ -> id)
        <+ recT (\ _ -> extractT t) mconcat

  oneT t = nonRecT (extractT t) (\ _ -> id)
        <+ recT' (\ _ -> extractT t) catchesM

  allR r = nonRecR (extractR r)
        <+ recAllR (\ _ -> extractR r)

  anyR r = nonRecR (extractR r)
        <+ recAnyR (\ _ -> extractR r)

  oneR r = nonRecR (extractR r)
        <+ recOneR (\ _ -> extractR r)

nonRecT :: TranslateH CoreExpr a -> (Id -> a -> b) -> TranslateH CoreBind b
nonRecT t f = translate $ \ c e -> case e of
                                     NonRec v e' -> f v <$> apply t (c @@ 0) e'
                                     _           -> fail "not NonRec constructor"

nonRecR :: RewriteH CoreExpr -> RewriteH CoreBind
nonRecR r = nonRecT r NonRec

recT' :: (Int -> TranslateH CoreDef a) -> ([HermitM a] -> HermitM b) -> TranslateH CoreBind b
recT' t f = translate $ \ c e -> case e of
         Rec bds -> -- Notice how we add the scoping bindings here *before* decending into each individual definition.
                    let c' = addBinding (Rec bds) c
                     in f [ apply (t n) (c' @@ n) (Def v e') -- here we convert from (Id,CoreExpr) to CoreDef
                          | ((v,e'),n) <- zip bds [0..]
                          ]
         _       -> fail "not Rec constructor"

recT :: (Int -> TranslateH CoreDef a) -> ([a] -> b) -> TranslateH CoreBind b
recT ts f = recT' ts (fmap f . sequence)

recAllR :: (Int -> RewriteH CoreDef) -> RewriteH CoreBind
recAllR rs = recT rs defToRecBind

recAnyR :: (Int -> RewriteH CoreDef) -> RewriteH CoreBind
recAnyR rs = recT' (attemptR . rs) (attemptAnyN defToRecBind)

recOneR :: (Int -> RewriteH CoreDef) -> RewriteH CoreBind
recOneR rs = recT' (withArgumentT . rs) (attemptOneN defToRecBind)

---------------------------------------------------------------------

instance Injection CoreDef Core where
  inject                = DefCore
  retract (DefCore def) = Just def
  retract _             = Nothing

instance Node CoreDef where
  type Generic CoreDef = Core

  numChildren _ = 1

instance Walker Context HermitM CoreDef where
  childL 0 = lens $ defT exposeT (childL1of2 Def)
  childL n = failT (missingChild n)

defT :: TranslateH CoreExpr a -> (Id -> a -> b) -> TranslateH CoreDef b
defT t f = translate $ \ c (Def v e) -> f v <$> apply t (c @@ 0) e

defR :: RewriteH CoreExpr -> RewriteH CoreDef
defR r = defT r Def

---------------------------------------------------------------------

instance Injection CoreAlt Core where
  inject                 = AltCore
  retract (AltCore expr) = Just expr
  retract _              = Nothing

instance Node CoreAlt where
  type Generic CoreAlt = Core

  numChildren _ = 1

instance Walker Context HermitM CoreAlt where
  childL 0 = lens $ altT exposeT (childL2of3 (,,))
  childL n = failT (missingChild n)

altT :: TranslateH CoreExpr a -> (AltCon -> [Id] -> a -> b) -> TranslateH CoreAlt b
altT t f = translate $ \ c (con,bs,e) -> f con bs <$> apply t (foldr addLambdaBinding c bs @@ 0) e

altR :: RewriteH CoreExpr -> RewriteH CoreAlt
altR r = altT r (,,)

---------------------------------------------------------------------

instance Injection CoreExpr Core where
  inject                  = ExprCore
  retract (ExprCore expr) = Just expr
  retract _               = Nothing

instance Node CoreExpr where
  type Generic CoreExpr = Core

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

instance Walker Context HermitM CoreExpr where

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
       caseChooseL = whenM (arr $ hasChild n) $
                           caseT idR (const exposeT) (\ e v t -> childLMofN (n-1) (Case e v t))

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

  oneT t = appT' (extractT t) (extractT t) (<<+)
        <+ lamT (extractT t) (\ _ -> id)
        <+ letT' (extractT t) (extractT t) (<<+)
        <+ caseT' (extractT t) (\ _ -> extractT t) (\ _ _ r rs -> catchesM (r:rs))
        <+ castT (extractT t) const
        <+ tickT (extractT t) (\ _ -> id)

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

  anyR r = appAnyR (extractR r) (extractR r)
        <+ lamR (extractR r)
        <+ letAnyR (extractR r) (extractR r)
        <+ caseAnyR (extractR r) (\ _ -> extractR r)
        <+ castR (extractR r)
        <+ tickR (extractR r)
        <+ fail "anyR failed"

  oneR r = appOneR (extractR r) (extractR r)
        <+ lamR (extractR r)
        <+ letOneR (extractR r) (extractR r)
        <+ caseOneR (extractR r) (\ _ -> extractR r)
        <+ castR (extractR r)
        <+ tickR (extractR r)
        <+ fail "oneR failed"

---------------------------------------------------------------------

-- Expr
varT :: (Id -> b) -> TranslateH CoreExpr b
varT f = contextfreeT $ \ e -> case e of
        Var n -> pure (f n)
        _     -> fail "no match for Var"

litT :: (Literal -> b) -> TranslateH CoreExpr b
litT f = contextfreeT $ \ e -> case e of
        Lit i -> pure (f i)
        _     -> fail "no match for Lit"


appT' :: TranslateH CoreExpr a1 -> TranslateH CoreExpr a2 -> (HermitM a1 -> HermitM a2 -> HermitM b) -> TranslateH CoreExpr b
appT' t1 t2 f = translate $ \ c e -> case e of
         App e1 e2 -> f (apply t1 (c @@ 0) e1) (apply t2 (c @@ 1) e2)
         _         -> fail "no match for App"

appT :: TranslateH CoreExpr a1 -> TranslateH CoreExpr a2 -> (a1 -> a2 -> b) -> TranslateH CoreExpr b
appT t1 t2 = appT' t1 t2 . liftA2

appAllR :: RewriteH CoreExpr -> RewriteH CoreExpr -> RewriteH CoreExpr
appAllR r1 r2 = appT r1 r2 App

appAnyR :: RewriteH CoreExpr -> RewriteH CoreExpr -> RewriteH CoreExpr
appAnyR r1 r2 = appT' (attemptR r1) (attemptR r2) (attemptAny2 App)

appOneR :: RewriteH CoreExpr -> RewriteH CoreExpr -> RewriteH CoreExpr
appOneR r1 r2 = appT' (withArgumentT r1) (withArgumentT r2) (attemptOne2 App)


lamT :: TranslateH CoreExpr a -> (Id -> a -> b) -> TranslateH CoreExpr b
lamT t f = translate $ \ c e -> case e of
        Lam b e1 -> f b <$> apply t (addLambdaBinding b c @@ 0) e1
        _        -> fail "no match for Lam"

lamR :: RewriteH CoreExpr -> RewriteH CoreExpr
lamR r = lamT r Lam


letT' :: TranslateH CoreBind a1 -> TranslateH CoreExpr a2 -> (HermitM a1 -> HermitM a2 -> HermitM b) -> TranslateH CoreExpr b
letT' t1 t2 f = translate $ \ c e -> case e of
        Let bds e1 -> f (apply t1 (c @@ 0) bds) (apply t2 (addBinding bds c @@ 1) e1)
                -- use *original* env, because the bindings are self-binding,
                -- if they are recursive. See allR (Rec ...) for details.
        _         -> fail "no match for Let"

letT :: TranslateH CoreBind a1 -> TranslateH CoreExpr a2 -> (a1 -> a2 -> b) -> TranslateH CoreExpr b
letT t1 t2 = letT' t1 t2 . liftA2

letAllR :: RewriteH CoreBind -> RewriteH CoreExpr -> RewriteH CoreExpr
letAllR r1 r2 = letT r1 r2 Let

letAnyR :: RewriteH CoreBind -> RewriteH CoreExpr -> RewriteH CoreExpr
letAnyR r1 r2 = letT' (attemptR r1) (attemptR r2) (attemptAny2 Let)

letOneR :: RewriteH CoreBind -> RewriteH CoreExpr -> RewriteH CoreExpr
letOneR r1 r2 = letT' (withArgumentT r1) (withArgumentT r2) (attemptOne2 Let)


caseT' :: TranslateH CoreExpr a1
      -> (Int -> TranslateH CoreAlt a2)
      -> (Id -> Type -> HermitM a1 -> [HermitM a2] -> HermitM b)
      -> TranslateH CoreExpr b
caseT' t ts f = translate $ \ c e -> case e of
         Case e1 b ty alts -> f b ty (apply t (c @@ 0) e1) $ let c' = addBinding (NonRec b e1) c
                                                                 in [ apply (ts n) (c' @@ (n+1)) alt
                                                                    | (alt,n) <- zip alts [0..]
                                                                    ]
         _ -> fail "no match for Case"

caseT :: TranslateH CoreExpr a1
      -> (Int -> TranslateH CoreAlt a2)
      -> (a1 -> Id -> Type -> [a2] -> b)
      -> TranslateH CoreExpr b
caseT t ts f = caseT' t ts (\ b ty me malts -> f <$> me <*> pure b <*> pure ty <*> sequence malts)

caseAllR :: RewriteH CoreExpr -> (Int -> RewriteH CoreAlt) -> RewriteH CoreExpr
caseAllR r rs = caseT r rs Case

caseAnyR :: RewriteH CoreExpr -> (Int -> RewriteH CoreAlt) -> RewriteH CoreExpr
caseAnyR r rs = caseT' (attemptR r) (attemptR . rs) (\ b ty -> attemptAny1N (\ e -> Case e b ty))

caseOneR :: RewriteH CoreExpr -> (Int -> RewriteH CoreAlt) -> RewriteH CoreExpr
caseOneR r rs = caseT' (withArgumentT r) (withArgumentT . rs) (\ b ty -> attemptOne1N (\ e -> Case e b ty))


castT :: TranslateH CoreExpr a -> (a -> Coercion -> b) -> TranslateH CoreExpr b
castT t f = translate $ \ c e -> case e of
                                   Cast e1 cast -> f <$> apply t (c @@ 0) e1 <*> pure cast
                                   _            -> fail "no match for Cast"

castR :: RewriteH CoreExpr -> RewriteH CoreExpr
castR r = castT r Cast


tickT :: TranslateH CoreExpr a -> (Tickish Id -> a -> b) -> TranslateH CoreExpr b
tickT t f = translate $ \ c e -> case e of
        Tick tk e1 -> f tk <$> apply t (c @@ 0) e1
        _          -> fail "no match for Tick"

tickR :: RewriteH CoreExpr -> RewriteH CoreExpr
tickR r = tickT r Tick

typeT :: (Type -> b) -> TranslateH CoreExpr b
typeT f = contextfreeT $ \ e -> case e of
                                  Type i -> pure (f i)
                                  _      -> fail "no match for Type"

coercionT :: (Coercion -> b) -> TranslateH CoreExpr b
coercionT f = contextfreeT $ \ e -> case e of
                                      Coercion i -> pure (f i)
                                      _          -> fail "no match for Coercion"

---------------------------------------------------------------------

-- Some additional congruence combinators to export.

letNonRecT :: TranslateH CoreExpr a1 -> TranslateH CoreExpr a2 -> (Id -> a1 -> a2 -> b) -> TranslateH CoreExpr b
letNonRecT t1 t2 f = letT (nonRecT t1 (,)) t2 (uncurry f)

letNonRecAllR :: RewriteH CoreExpr -> RewriteH CoreExpr -> RewriteH CoreExpr
letNonRecAllR r1 r2 = letAllR (nonRecR r1) r2

letNonRecAnyR :: RewriteH CoreExpr -> RewriteH CoreExpr -> RewriteH CoreExpr
letNonRecAnyR r1 r2 = letAnyR (nonRecR r1) r2

letNonRecOneR :: RewriteH CoreExpr -> RewriteH CoreExpr -> RewriteH CoreExpr
letNonRecOneR r1 r2 = letOneR (nonRecR r1) r2


letRecT :: (Int -> TranslateH CoreDef a1) -> TranslateH CoreExpr a2 -> ([a1] -> a2 -> b) -> TranslateH CoreExpr b
letRecT ts t f = letT (recT ts id) t f

letRecAllR :: (Int -> RewriteH CoreDef) -> RewriteH CoreExpr -> RewriteH CoreExpr
letRecAllR rs r = letAllR (recAllR rs) r

letRecAnyR :: (Int -> RewriteH CoreDef) -> RewriteH CoreExpr -> RewriteH CoreExpr
letRecAnyR rs r = letAnyR (recAnyR rs) r

letRecOneR :: (Int -> RewriteH CoreDef) -> RewriteH CoreExpr -> RewriteH CoreExpr
letRecOneR rs r = letOneR (recOneR rs) r


recDefT :: (Int -> TranslateH CoreExpr a1) -> ([(Id,a1)] -> b) -> TranslateH CoreBind b
recDefT ts f = recT (\ n -> defT (ts n) (,)) f

recDefAllR :: (Int -> RewriteH CoreExpr) -> RewriteH CoreBind
recDefAllR rs = recAllR (\ n -> defR (rs n))

recDefAnyR :: (Int -> RewriteH CoreExpr) -> RewriteH CoreBind
recDefAnyR rs = recAnyR (\ n -> defR (rs n))

recDefOneR :: (Int -> RewriteH CoreExpr) -> RewriteH CoreBind
recDefOneR rs = recOneR (\ n -> defR (rs n))


letRecDefT :: (Int -> TranslateH CoreExpr a1) -> TranslateH CoreExpr a2 -> ([(Id,a1)] -> a2 -> b) -> TranslateH CoreExpr b
letRecDefT ts t f = letRecT (\ n -> defT (ts n) (,)) t f

letRecDefAllR :: (Int -> RewriteH CoreExpr) -> RewriteH CoreExpr -> RewriteH CoreExpr
letRecDefAllR rs r = letRecAllR (\ n -> defR (rs n)) r

letRecDefAnyR :: (Int -> RewriteH CoreExpr) -> RewriteH CoreExpr -> RewriteH CoreExpr
letRecDefAnyR rs r = letRecAnyR (\ n -> defR (rs n)) r

letRecDefOneR :: (Int -> RewriteH CoreExpr) -> RewriteH CoreExpr -> RewriteH CoreExpr
letRecDefOneR rs r = letRecOneR (\ n -> defR (rs n)) r

---------------------------------------------------------------------