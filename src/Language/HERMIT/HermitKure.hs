{-# LANGUAGE MultiParamTypeClasses, TypeFamilies, FlexibleInstances, FlexibleContexts, TupleSections #-}

module Language.HERMIT.HermitKure
       (
         TranslateH
       , RewriteH
       , LensH
       , Core(..)
       -- Scoping Combinators
       , modGutsT
       , listBindT
       , nonRecT
       , recT
       , altT
       , varT
       , litT
       , appT
       , lamT
       , letT
       , caseT
       , castT
       , tickT
       , typeT
       , coercionT
       , letNonRecT
       , letRecT
       -- Useful Translations
       , pathT
       )
where

import GhcPlugins hiding (empty)

import Language.KURE

import Language.HERMIT.HermitEnv
import Language.HERMIT.HermitMonad

import Control.Applicative
import Data.Monoid

---------------------------------------------------------------------

type TranslateH a b = Translate HermitEnv HermitM a b
type RewriteH a = Rewrite HermitEnv HermitM a
type LensH a b = Lens HermitEnv HermitM a b

---------------------------------------------------------------------

-- | NOTE: 'Type' is not included in the generic datatype.
--   However, we could have included it and provided the facility for descending into types.
--   We have not done so because
--     (a) we do not need that functionality, and
--     (b) the types are complicated and we're not sure that we understand them.

data Core = ModGutsCore  ModGuts
          | ProgramCore  CoreProgram
          | BindCore     CoreBind
          | ExprCore     CoreExpr
          | AltCore      CoreAlt

---------------------------------------------------------------------

instance Term Core where
  type Generic Core = Core

-- Defining Walker instances for the Generic type 'Core' is almost entirely automated by KURE.
-- Unfortunately, you still need to pattern match on the 'Core' data type.

instance WalkerR HermitEnv HermitM Core where
  allR rr = rewrite $ \ c core -> case core of
          ModGutsCore x -> allRgeneric rr c x
          ProgramCore x -> allRgeneric rr c x
          BindCore x    -> allRgeneric rr c x
          ExprCore x    -> allRgeneric rr c x
          AltCore x     -> allRgeneric rr c x

  anyR rr = rewrite $ \ c core -> case core of
          ModGutsCore x -> anyRgeneric rr c x
          ProgramCore x -> anyRgeneric rr c x
          BindCore x    -> anyRgeneric rr c x
          ExprCore x    -> anyRgeneric rr c x
          AltCore x     -> anyRgeneric rr c x

instance Monoid b => WalkerT HermitEnv HermitM Core b where
  crushT tt = translate $ \ c core -> case core of
          ModGutsCore x -> crushTgeneric tt c x
          ProgramCore x -> crushTgeneric tt c x
          BindCore x    -> crushTgeneric tt c x
          ExprCore x    -> crushTgeneric tt c x
          AltCore x     -> crushTgeneric tt c x

instance WalkerL HermitEnv HermitM Core where
  chooseL n = translate $ \ c core -> case core of
          ModGutsCore x -> chooseLgeneric n c x
          ProgramCore x -> chooseLgeneric n c x
          BindCore x    -> chooseLgeneric n c x
          ExprCore x    -> chooseLgeneric n c x
          AltCore x     -> chooseLgeneric n c x

---------------------------------------------------------------------

instance Injection ModGuts Core where
  inject                     = ModGutsCore
  retract (ModGutsCore guts) = Just guts
  retract _                  = Nothing

instance Term ModGuts where
  type Generic ModGuts = Core

instance WalkerR HermitEnv HermitM ModGuts where
  allR rr = modGutsT (extractR rr) (\ modGuts bds -> modGuts {mg_binds = bds})

  anyR = allR -- only one interesting child, allR and anyR behave the same

instance  Monoid b => WalkerT HermitEnv HermitM ModGuts b where
  crushT tt = modGutsT (extractT tt) ( \ _ b -> b)

instance WalkerL HermitEnv HermitM ModGuts where
  chooseL 0 = modGutsT exposeT (\ modGuts cx -> (cx, \ bds -> pure $ modGuts { mg_binds = bds })) `composeL` promoteL
  chooseL n = missingChildL n

-- slightly different; passes in *all* of the original
modGutsT :: TranslateH CoreProgram a -> (ModGuts -> a -> b) -> TranslateH ModGuts b
modGutsT tt f = translate $ \ c modGuts -> f modGuts <$> apply tt (c @@ 0) (mg_binds modGuts)

---------------------------------------------------------------------

instance Injection CoreProgram Core where
  inject                     = ProgramCore
  retract (ProgramCore guts) = Just guts
  retract _                  = Nothing

instance Term CoreProgram where
  type Generic CoreProgram = Core

instance WalkerR HermitEnv HermitM CoreProgram where
  allR rr = listBindT [] (extractR rr) (extractR rr) (:)

  anyR rr = consBindT' (attemptR $ extractR rr) (attemptR $ extractR rr) (attemptAny2 (:))

instance Monoid b => WalkerT HermitEnv HermitM CoreProgram b where
  crushT tt = listBindT mempty (extractT tt) (extractT tt) mappend

instance WalkerL HermitEnv HermitM CoreProgram where
  chooseL 0 = consBindT exposeT idR (\ cx es -> (cx, \ e  -> pure (e:es))) `composeL` promoteL
  chooseL 1 = consBindT idR exposeT (\ e  cx -> (cx, \ es -> pure (e:es))) `composeL` promoteL
  chooseL n = missingChildL n

nilT' :: HermitM b -> TranslateH [a] b
nilT' b = liftMT $ \ as -> if null as then b else fail "no match for nilT"

consBindT' :: TranslateH CoreBind a1 -> TranslateH [CoreBind] a2 -> (HermitM a1 -> HermitM a2 -> HermitM b) -> TranslateH [CoreBind] b
consBindT' t1 t2 f = translate $ \ c e -> case e of
        bd:bds -> f (apply t1 (c @@ 0) bd) (apply t2 (addHermitBinding bd c @@ 1) bds)
        _      -> fail "no match for consBindT"

consBindT :: TranslateH CoreBind a1 -> TranslateH [CoreBind] a2 -> (a1 -> a2 -> b) -> TranslateH [CoreBind] b
consBindT t1 t2 f = consBindT' t1 t2 (liftA2 f)

listBindT :: b -> TranslateH CoreBind a1 -> TranslateH [CoreBind] a2 -> (a1 -> a2 -> b) -> TranslateH [CoreBind] b
listBindT b t1 t2 f = consBindT t1 t2 f <+ nilT' (pure b)

---------------------------------------------------------------------

instance Injection CoreBind Core where
  inject                  = BindCore
  retract (BindCore expr) = Just expr
  retract _               = Nothing

instance Term CoreBind where
  type Generic CoreBind = Core

instance WalkerR HermitEnv HermitM CoreBind where
  allR rr =    nonRecT (extractR rr) NonRec
            <+ recT (const $ extractR rr) Rec

  anyR rr =    nonRecT (extractR rr) NonRec
            <+ recT' (const $ attemptR $ extractR rr) (attemptAnyN Rec . (map.liftA) (\ (v,(b,e)) -> (b,(v,e))))

instance  Monoid b => WalkerT HermitEnv HermitM CoreBind b where
  crushT tt = nonRecT (extractT tt) (\ _ r -> r) <+ recT (const $ extractT tt) (mconcat . map snd)

instance WalkerL HermitEnv HermitM CoreBind where
  chooseL n = case n of
                0 -> nonrec <+ rec
                _ -> rec
     where
         nonrec = nonRecT exposeT (\ v cx -> (cx, pure . NonRec v)) `composeL` promoteL
         rec    = do
            -- find the number of binds
            sz <- recT (const idR) length
            if n < 0 || n >= sz
                then missingChildL n
                     -- if in range, then figure out context
                else recT (const exposeT)
                          (\ bds -> (snd (bds !! n)
                                    , \ e -> return $ Rec
                                                [ (v', if i == n then e else e')
                                                | ((v',(_,e')),i) <- zip bds [0..]
                                                ]
                                    )
                          ) `composeL` promoteL

nonRecT :: TranslateH CoreExpr a -> (Id -> a -> b) -> TranslateH CoreBind b
nonRecT tt f = translate $ \ c e -> case e of
                                      NonRec v e' -> f v <$> apply tt (c @@ 0) e'
                                      _           -> fail "nonRecT: not NonRec"

recT' :: (Int -> TranslateH CoreExpr a) -> ([HermitM (Id,a)] -> HermitM b) -> TranslateH CoreBind b
recT' tt f = translate $ \ c e -> case e of
         Rec bds -> -- Notice how we add the scoping bindings here *before* decending into the rhss.
                    let c' = addHermitBinding (Rec bds) c
                     in f [ (v,) <$> apply (tt n) (c' @@ n) e1
                          | ((v,e1),n) <- zip bds [0..]
                          ]
         _       -> fail "recT: not Rec"

recT :: (Int -> TranslateH CoreExpr a) -> ([(Id,a)] -> b) -> TranslateH CoreBind b
recT tt f = recT' tt (fmap f . sequence)

---------------------------------------------------------------------

instance Injection CoreAlt Core where
  inject                 = AltCore
  retract (AltCore expr) = Just expr
  retract _              = Nothing

instance Term CoreAlt where
  type Generic CoreAlt = Core

instance WalkerR HermitEnv HermitM CoreAlt where
  allR rr = altT (extractR rr) (,,)
  anyR = allR -- only one interesting child, allR and anyR behave the same

instance  Monoid b => WalkerT HermitEnv HermitM CoreAlt b where
  crushT tt = altT (extractT tt) (\ _ _ r -> r)

instance WalkerL HermitEnv HermitM CoreAlt where
  chooseL 0 = altT exposeT (\ con bs cx -> (cx, \ e -> pure (con,bs,e))) `composeL` promoteL
  chooseL n = missingChildL n

altT :: TranslateH CoreExpr a -> (AltCon -> [Id] -> a -> b) -> TranslateH CoreAlt b
altT tt f = translate $ \ c (con,bs,e) -> f con bs <$> apply tt (foldr addHermitEnvLambdaBinding c bs @@ 0) e

---------------------------------------------------------------------

instance Injection CoreExpr Core where
  inject                  = ExprCore
  retract (ExprCore expr) = Just expr
  retract _               = Nothing

instance Term CoreExpr where
  type Generic CoreExpr = Core

instance WalkerR HermitEnv HermitM CoreExpr where

  allR rr =     varT Var
             <+ litT Lit
             <+ appT (extractR rr) (extractR rr) App
             <+ lamT (extractR rr) Lam
             <+ letT (extractR rr) (extractR rr) Let
             <+ caseT (extractR rr) (const $ extractR rr) Case
             <+ castT (extractR rr) Cast
             <+ tickT (extractR rr) Tick
             <+ typeT Type
             <+ coercionT Coercion
             <+ fail "allR failed for all Expr constructors"

  anyR rr =     appT' (attemptR $ extractR rr) (attemptR $ extractR rr) (attemptAny2 App)
             <+ lamT (extractR rr) Lam
             <+ letT' (attemptR $ extractR rr) (attemptR $ extractR rr) (attemptAny2 Let)
             <+ caseT' (attemptR $ extractR rr) (const $ attemptR $ extractR rr) (\ b ty -> attemptAny1N (\ e alts -> Case e b ty alts))
             <+ castT (extractR rr) Cast
             <+ tickT (extractR rr) Tick
             <+ fail "anyR failed for all Expr constructors"

instance  Monoid b => WalkerT HermitEnv HermitM CoreExpr b where
  crushT tt = varT (const mempty)
           <+ litT (const mempty)
           <+ appT (extractT tt) (extractT tt) mappend
           <+ lamT (extractT tt) (\ _ r -> r)
           <+ letT (extractT tt) (extractT tt) mappend
           <+ caseT (extractT tt) (const $ extractT tt) (\ r _ _ rs -> mconcat (r:rs))
           <+ castT (extractT tt) (\ r _ -> r)
           <+ tickT (extractT tt) (\ _ r -> r)
           <+ typeT (const mempty)
           <+ coercionT (const mempty)
           <+ fail "crushT failed for all Expr constructors"

instance WalkerL HermitEnv HermitM CoreExpr where
  chooseL 0 = ( appT  exposeT idR         (\ cx e2       -> (cx, \ e1 -> pure $ App e1 e2) )        `composeL` promoteL )
           <+ ( lamT  exposeT             (\ v cx        -> (cx, \ e1 -> pure $ Lam v e1) )         `composeL` promoteL )
           <+ ( letT  exposeT idR         (\ cx e2       -> (cx, \ bd -> pure $ Let bd e2) )        `composeL` promoteL )
           <+ ( caseT exposeT (const idR) (\ cx v t alts -> (cx, \ e1 -> pure $ Case e1 v t alts) ) `composeL` promoteL )
           <+ ( castT exposeT             (\ cx c        -> (cx, \ e1 -> pure $ Cast e1 c) )        `composeL` promoteL )
           <+ ( tickT exposeT             (\ t cx        -> (cx, \ e1 -> pure $ Tick t e1) )        `composeL` promoteL )

  chooseL 1 = ( appT idR exposeT          (\ e1 cx       -> (cx, \ e2 -> pure $ App e1 e2) )        `composeL` promoteL )
           <+ ( letT idR exposeT          (\ bd cx       -> (cx, \ e2 -> pure $ Let bd e2) )        `composeL` promoteL )
           <+ caseChooseL 1 `composeL` promoteL

  chooseL n = caseChooseL n `composeL` promoteL


caseChooseL :: Int -> LensH CoreExpr CoreAlt
caseChooseL n = do Case _ _ _ alts <- idR
                   if n < 1 || n > length alts
                    then missingChildL n
                    else caseT idR (const exposeT)
                                   (\ e v t calts -> ( calts !! (n - 1)
                                                     , \ alt -> return $ Case e v t
                                                               [ if i == n then alt else alt'
                                                               | ((_,alt'),i) <- zip calts [1..]
                                                               ]
                                                     )
                                   )

---------------------------------------------------------------------

-- These are scoping aware combinators.
-- The primed versions are the generalisations needed to define "anyR".

-- Expr
varT :: (Id -> b) -> TranslateH CoreExpr b
varT f = liftMT $ \ e -> case e of
        Var n -> pure (f n)
        _     -> fail "no match for Var"

litT :: (Literal -> b) -> TranslateH CoreExpr b
litT f = liftMT $ \ e -> case e of
        Lit i -> pure (f i)
        _     -> fail "no match for Lit"

appT' :: TranslateH CoreExpr a1 -> TranslateH CoreExpr a2 -> (HermitM a1 -> HermitM a2 -> HermitM b) -> TranslateH CoreExpr b
appT' lhs rhs f = translate $ \ c e -> case e of
         App e1 e2 -> f (apply lhs (c @@ 0) e1) (apply rhs (c @@ 1) e2)
         _         -> fail "no match for App"

appT :: TranslateH CoreExpr a1 -> TranslateH CoreExpr a2 -> (a1 -> a2 -> b) -> TranslateH CoreExpr b
appT lhs rhs f = appT' lhs rhs (liftA2 f)

lamT :: TranslateH CoreExpr a -> (Id -> a -> b) -> TranslateH CoreExpr b
lamT tt f = translate $ \ c e -> case e of
        Lam b e1 -> f b <$> apply tt (addHermitEnvLambdaBinding b c @@ 0) e1
        _        -> fail "no match for Lam"

letT' :: TranslateH CoreBind a1 -> TranslateH CoreExpr a2 -> (HermitM a1 -> HermitM a2 -> HermitM b) -> TranslateH CoreExpr b
letT' bdsT exprT f = translate $ \ c e -> case e of
        Let bds e1 -> f (apply bdsT (c @@ 0) bds) (apply exprT (addHermitBinding bds c @@ 1) e1)
                -- use *original* env, because the bindings are self-binding,
                -- if they are recursive. See allR (Rec ...) for details.
        _         -> fail "no match for Let"

letT :: TranslateH CoreBind a1 -> TranslateH CoreExpr a2 -> (a1 -> a2 -> b) -> TranslateH CoreExpr b
letT bdsT exprT f = letT' bdsT exprT (liftA2 f)

caseT' :: TranslateH CoreExpr a1
      -> (Int -> TranslateH CoreAlt a2)          -- Int argument *starts* at 1.
      -> (Id -> Type -> HermitM a1 -> [HermitM a2] -> HermitM b)
      -> TranslateH CoreExpr b
caseT' exprT altnT f = translate $ \ c e -> case e of
         Case e1 b ty alts -> f b ty (apply exprT (c @@ 0) e1) $ let c' = addHermitBinding (NonRec b e1) c
                                                                  in [ apply (altnT n) (c' @@ n) alt
                                                                     | (alt,n) <- zip alts [1..]
                                                                     ]
         _ -> fail "no match for Case"

caseT :: TranslateH CoreExpr a1
      -> (Int -> TranslateH CoreAlt a2)          -- Int argument *starts* at 1.
      -> (a1 -> Id -> Type -> [a2] -> b)
      -> TranslateH CoreExpr b
caseT exprT altnT f = caseT' exprT altnT (\ b ty me malts -> f <$> me <*> pure b <*> pure ty <*> sequence malts)

castT :: TranslateH CoreExpr a -> (a -> Coercion -> b) -> TranslateH CoreExpr b
castT tt f = translate $ \ c e -> case e of
        Cast e1 cast -> f <$> apply tt (c @@ 0) e1 <*> pure cast
        _            -> fail "no match for Cast"

tickT :: TranslateH CoreExpr a -> (Tickish Id -> a -> b) -> TranslateH CoreExpr b
tickT tt f = translate $ \ c e -> case e of
        Tick tk e1 -> f tk <$> apply tt (c @@ 0) e1
        _          -> fail "no match for Tick"

typeT :: (Type -> b) -> TranslateH CoreExpr b
typeT f = liftMT $ \ e -> case e of
                            Type i -> pure (f i)
                            _      -> fail "no match for Type"

coercionT :: (Coercion -> b) -> TranslateH CoreExpr b
coercionT f = liftMT $ \ e -> case e of
                                Coercion i -> pure (f i)
                                _          -> fail "no match for Coercion"

---------------------------------------------------------------------

-- Some additional scoping combinators to export.

letNonRecT :: TranslateH CoreExpr a1 -> TranslateH CoreExpr a2 -> (Id -> a1 -> a2 -> b) -> TranslateH CoreExpr b
letNonRecT t1 t2 f = letT (nonRecT t1 (,)) t2 (uncurry f)

letRecT :: (Int -> TranslateH CoreExpr a1) -> TranslateH CoreExpr a2 -> ([(Id,a1)] -> a2 -> b) -> TranslateH CoreExpr b
letRecT t1s t2 f = letT (recT t1s id) t2 f

---------------------------------------------------------------------

-- Useful Translations

-- | 'pathT' finds the current path.
pathT :: TranslateH a ContextPath
pathT = fmap hermitBindingPath contextT

---------------------------------------------------------------------
