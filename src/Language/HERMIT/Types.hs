{-# LANGUAGE MultiParamTypeClasses, TypeFamilies, FlexibleInstances, FlexibleContexts, TupleSections #-}

module Language.HERMIT.Types where

import GhcPlugins hiding (empty)

import Language.KURE

import Language.HERMIT.HermitEnv
import Language.HERMIT.HermitMonad

import Control.Applicative
import Control.Arrow (second)
import Data.Monoid

----------------------------------------------------------------------------

type TranslateH a b = Translate HermitEnv HermitM a b
type RewriteH a = Rewrite HermitEnv HermitM a
type LensH a b = Lens HermitEnv HermitM a b

---------------------------------------------------------------------

data Core
        = ModGutsCore   ModGuts
        | ProgramCore   CoreProgram
        | BindCore      (Bind Id)
        | ExprCore      (Expr Id)
--        | AltListCore   [Alt Id]
        | AltCore       (Alt Id)
        | TypeCore      Type

---------------------------------------------------------------------

instance Term Core where
  type Generic Core = Core

instance WalkerR HermitEnv HermitM Core where
  allR rr = rewrite $ \ c blob -> case blob of
          -- Going from Core to sub-Core is the one case where you do not augment the path,
          -- but instead direct traffic.
          ModGutsCore modGuts -> ModGutsCore <$> apply (allR rr) c modGuts
          ProgramCore prog    -> ProgramCore <$> apply (allR rr) c prog
          BindCore    bind    -> BindCore    <$> apply (allR rr) c bind
          ExprCore    expr    -> ExprCore    <$> apply (allR rr) c expr
          AltCore     alt     -> AltCore     <$> apply (allR rr) c alt

instance Monoid b => WalkerT HermitEnv HermitM Core b where
  crushT tt = translate $ \ c blob -> case blob of
          ModGutsCore x -> apply (crushT tt) c x
          ProgramCore x -> apply (crushT tt) c x
          BindCore x    -> apply (crushT tt) c x
          ExprCore x    -> apply (crushT tt) c x
          AltCore x     -> apply (crushT tt) c x

instance WalkerL HermitEnv HermitM Core where
  chooseL n = translate $ \ c blob -> case blob of
          -- Going from Core to sub-Core is the one case where you do not augment the path,
          -- but instead direct traffic.
          ModGutsCore x -> act c x
          ProgramCore x -> act c x
          BindCore x    -> act c x
          ExprCore x    -> act c x
          AltCore x     -> act c x

     where
       act :: (WalkerL HermitEnv HermitM a, Generic a ~ Core)
              => HermitEnv -> a -> HermitM ((HermitEnv, Core), Core -> HermitM Core)
       act c a = (second.result.fmap) inject <$> apply (chooseL n) c a

       -- act c a = do (cb, fn) <- apply (chooseL n) c a
       --              return (cb, liftA inject . fn)
              
       -- act c a = do (cb, fn) <- apply (chooseL n) c a
       --              return (cb, retractWith (liftA inject . fn))
                    
               -- act c a = do ((c',b), fn) <- apply (chooseL n) c a
               --              return ((c',inject b), retractWith (liftA inject . fn))

                 -- act cxt = do
                 -- (cb, fn) <- apply (chooseL n) cxt
                 -- return $ (fmap inject cb, \ b -> case retract b of
                 --                               Nothing -> fail "oneL failed"
                 --                               Just b -> liftM inject (fn b))

result :: (b -> c) -> (a -> b) -> (a -> c)
result = (.)

---------------------------------------------------------------------

instance Injection ModGuts Core where
  inject                     = ModGutsCore
  retract (ModGutsCore guts) = Just guts
  retract _                  = Nothing

instance Term ModGuts where
  type Generic ModGuts = Core

instance WalkerR HermitEnv HermitM ModGuts where
  allR rr = rewrite $ \ c modGuts -> do
          binds' <- apply (extractR rr) (c @@ 0) (mg_binds modGuts)
          return (modGuts { mg_binds = binds' })

instance  Monoid b => WalkerT HermitEnv HermitM ModGuts b where
  crushT tt = modGutsT (extractT tt) ( \ _ r -> r)

instance WalkerL HermitEnv HermitM ModGuts where
  chooseL 0 = modGutsT contextidT (\ modGuts cxt -> (cxt, \ prog -> return $ modGuts { mg_binds = prog })) `composeL` promoteL
  chooseL _ = failL

modGutsT :: TranslateH CoreProgram a1
         -> (ModGuts -> a1 -> a)                -- slightly different; passes in *all* of the original
         -> TranslateH ModGuts a
modGutsT tt comp = translate $ \ c modGuts -> comp modGuts <$> apply tt (c @@ 0) (mg_binds modGuts)

---------------------------------------------------------------------

instance Injection CoreProgram Core where
  inject                     = ProgramCore
  retract (ProgramCore guts) = Just guts
  retract _                  = Nothing

instance Term CoreProgram where
  type Generic CoreProgram = Core

instance WalkerR HermitEnv HermitM CoreProgram where
  allR rr = rewrite $ \ c prog -> case prog of
          []       -> pure []
          (bd:bds) -> (:) <$> apply (extractR rr) (c @@ 0) bd <*> apply (extractR rr) (addHermitBinding bd c @@ 1) bds

instance Monoid b => WalkerT HermitEnv HermitM CoreProgram b where
  crushT tt = consBindT (extractT tt) (extractT tt) mappend <+ nilT mempty

instance WalkerL HermitEnv HermitM CoreProgram where
  chooseL 0 = consBindT contextidT idR (\ cxt e2 -> (cxt, \ e1 -> return $ e1 : e2)) `composeL` promoteL
  chooseL 1 = consBindT idR contextidT (\ e1 cxt -> (cxt, \ e2 -> return $ e1 : e2)) `composeL` promoteL
  chooseL _ = failL

consBindT :: (a ~ CoreBind)
      => TranslateH a a1
      -> TranslateH [a] a2
      -> (a1 -> a2 -> b)
      -> TranslateH [a] b
consBindT t1 t2 f = translate $ \ c e -> case e of
        (bd:bds) -> f <$> apply t1 (c @@ 0) bd <*> apply t2 (addHermitBinding bd c @@ 1) bds
        _        -> fail "no match for consT"

---------------------------------------------------------------------

instance Injection (Bind Id) Core where
  inject                  = BindCore
  retract (BindCore expr) = Just expr
  retract _               = Nothing

instance Term (Bind Id) where
  type Generic (Bind Id) = Core

instance WalkerR HermitEnv HermitM (Bind Id) where
  allR rr = rewrite $ \ c e -> case e of
          NonRec n e1 -> NonRec n <$> apply (extractR rr) (c @@ 0) e1
          Rec bds     -> 
                  -- Notice how we add the scoping bindings
                  -- here *before* decending into the rhss.
                         let env' = addHermitBinding (Rec bds) c
                          in Rec <$> sequence
                                       [ (n,) <$> apply (extractR rr) (env' @@ i) e
                                       | ((n,e),i) <- zip bds [0..]
                                       ]

instance  Monoid b => WalkerT HermitEnv HermitM (Bind Id) b where
  crushT tt = nonRecT (extractT tt) (\ _ r -> r)
           <+ recT    (const $ extractT tt) (mconcat . map snd)

instance WalkerL HermitEnv HermitM (Bind Id) where
  chooseL n = case n of 
                0 -> nonrec <+ rec
                n -> rec
     where
         nonrec = nonRecT contextidT (\ v cxt -> (cxt, pure . NonRec v)) `composeL` promoteL
         rec    = do
            -- find the number of binds
            sz <- recT (const idR) length
            if n < 0 || n >= sz
                then failL
                     -- if in range, then figure out context
                else recT (\ _ -> contextidT)
                          (\ bds -> (snd (bds !! n)
                                    , \ e -> return $ Rec
                                                [ (v', if i == n then e else e')
                                                | ((v',(_,e')),i) <- zip bds [0..]
                                                ]
                                    )
                          ) `composeL` promoteL

{-
  chooseL 0 =
        <+ rec 0
  chooseL n = rec n
    where
     rec n = recT idR contextidT (\ e1 cxt -> (cxt, \ e2 -> return $ e1 : e2)) `composeL` promoteL
  chooseL _ = failL
-}

recT :: (Int -> TranslateH CoreExpr a1)
      -> ([(Id,a1)] -> b)
      -> TranslateH CoreBind b
recT tt comp = translate $ \ c e -> case e of
        Rec bds -> 
          -- Notice how we add the scoping bindings
          -- here *before* decending into the rhss.
                   let c' = addHermitBinding (Rec bds) c
                    in comp <$> sequence [ (v,) <$> apply (tt n) (c' @@ n) rhs
                                         | ((v,rhs),n) <- zip bds [0..]
                                         ]
        _       -> fail "recT: not Rec"

nonRecT :: (TranslateH CoreExpr a1)
      -> (Var -> a1 -> b)
      -> TranslateH CoreBind b
nonRecT tt comp = translate $ \ c e -> case e of
                                         NonRec v e' -> comp v <$> apply tt c e'
                                         _           -> fail "nonRecT: not NonRec"

---------------------------------------------------------------------

instance Injection (Expr Id) Core where
  inject                  = ExprCore
  retract (ExprCore expr) = Just expr
  retract _               = Nothing

instance Term (Expr Id) where
  type Generic (Expr Id) = Core

instance WalkerR HermitEnv HermitM (Expr Id) where
  allR rr = rewrite $ \ c e -> case e of
          Var {}    -> pure e
          Lit {}    -> pure e
          App e1 e2 -> App <$> apply (extractR rr) (c @@ 0) e1 
                           <*> apply (extractR rr) (c @@ 1) e2
          Lam b e   -> Lam b <$> apply (extractR rr) (addHermitEnvLambdaBinding b c @@ 0) e
          Let bds e -> Let <$> apply (extractR rr) (c @@ 0) bds 
                           <*> apply (extractR rr) (addHermitBinding bds c @@ 1) e
                       -- use *original* env, because the bindings are self-binding,
                       -- if they are recursive. See allR (Rec ...) for details.
          
          Case e b ty alts ->
                       do e' <- apply (extractR rr) (c @@ 0) e
                          let c' = addHermitBinding (NonRec b e) c
                          alts' <- sequence [ apply (extractR rr) (c' @@ i) alt
                                            | (alt,i) <- zip alts [1..]
                                            ]
                          return $ Case e' b ty alts'

          Cast e cast -> flip Cast cast <$> apply (extractR rr) (c @@ 0) e
          Tick tk e -> Tick tk <$> apply (extractR rr) (c @@ 0) e
                -- Not sure about this. Should be descend into the type here?
                -- If we do so, we should also descend into the types
                -- inside Coercion, Id, etc.
          Type _ty    -> pure e
          Coercion _c -> pure e

instance  Monoid b => WalkerT HermitEnv HermitM (Expr Id) b where
  crushT tt = varT (\ _ -> mempty)
           <+ litT (\ _ -> mempty)
           <+ appT (extractT tt) (extractT tt) mappend
           <+ lamT (extractT tt) (\ _ r -> r)
           <+ letT (extractT tt) (extractT tt) mappend
           <+ caseT (extractT tt) (const $ extractT tt) (\ r _ _ rs -> mconcat (r : rs))
           <+ castT (extractT tt) (\ r _ -> r)
           <+ tickT (extractT tt) (\ _ r -> r)
           <+ typeT (\ _ -> mempty)
           <+ coercionT (\ _ -> mempty)

instance WalkerL HermitEnv HermitM (Expr Id) where
  chooseL n = case n of
      0 -> (( appT contextidT idR  $ \ cxt e2       -> (cxt, \ e1 -> return $ App e1 e2) )        `composeL` promoteL )
        <+ (( lamT contextidT      $ \ v cxt        -> (cxt, \ e1 -> return $ Lam v e1) )         `composeL` promoteL )
        <+ (( letT contextidT idR  $ \ cxt e2       -> (cxt, \ bd -> return $ Let bd e2) )        `composeL` promoteL )
        <+ (( caseT contextidT (const idR)
                                   $ \ cxt v t alts -> (cxt, \ e1 -> return $ Case e1 v t alts) ) `composeL` promoteL )
        <+ (( castT contextidT     $ \ cxt c        -> (cxt, \ e1 -> return $ Cast e1 c) )        `composeL` promoteL )
        <+ (( tickT contextidT     $ \ t cxt        -> (cxt, \ e1 -> return $ Tick t e1) )        `composeL` promoteL )
      1 -> (( appT idR contextidT  $ \ e1 cxt       -> (cxt, \ e2 -> return $ App e1 e2) )        `composeL` promoteL )
        <+ (( letT idR contextidT  $ \ bd cxt       -> (cxt, \ e2 -> return $ Let bd e2) )        `composeL` promoteL )
        <+ caseChooseL
      n -> caseChooseL
    where
        caseChooseL = do
            sz <- caseT idR (const idR) $ \ _ _ _ alts -> length alts
            if n < 1 || n > sz
                then failL
                else caseT idR (const contextidT)
                               (\ e v t alts -> ( alts !! (n - 1)
                                                  , \ alt -> return $ Case e v t
                                                              [ if i == n then alt else alt'
                                                              | ((_,alt'),i) <- zip alts [1..]
                                                              ]
                                                  )
                               ) `composeL` promoteL

--        <+ (( caseT contextidT idR $ \ cxt v t alts -> (cxt, \ e1 -> return $ Case e1 v t alts) ) `composeL` promoteL )

--         foo cxt $ \ e1 -> App e1 e2 )

-- I don't think "foo" is used anywhere
-- foo :: (Alternative m, Term a, Term exp)
--      => (HermitEnv,a) -> (exp -> a1) -> ((HermitEnv,Generic a), Generic exp -> m a1)
-- foo (c,a) f = ((c,inject a), retractWithA f)

---------------------------------------------------------------------

{-
instance Term [Alt Id] where
  type Generic [Alt Id] = Core

  retract (AltListCore expr) = return expr
  retract _              = Nothing
  inject                = AltListCore

  allR rr = ( consT (extractR rr) (extractR rr) $ \ x xs -> x : xs )
         <+ ( nilT                              $ [] )

  crushT tt = ( consT (extractT tt) (extractT tt) $ mappend )
           <+ ( nilT                              $ mempty )

  crushT tt = ( consT (extractT tt) (extractT tt) $ mappend )
           <+ ( nilT                              $ mempty )

  chooseL 0 = consT contextidT idR  (\ cxt e2 -> (cxt, \ e1 -> return $ e1 : e2) )        `composeL` promoteL
  chooseL 1 = consT idR contextidT  (\ e1 cxt -> (cxt, \ e2 -> return $ e1 : e2) )        `composeL` promoteL
  chooseL _ = failL
-}

---------------------------------------------------------------------

instance Injection (Alt Id) Core where
  inject                 = AltCore
  retract (AltCore expr) = Just expr
  retract _              = Nothing

instance Term (Alt Id) where
  type Generic (Alt Id) = Core

instance WalkerR HermitEnv HermitM (Alt Id) where
  allR rr = rewrite $ \ c (con,bs,e) -> (con,bs,) <$> apply (extractR rr) (foldr addHermitEnvLambdaBinding c bs @@ 0) e

instance  Monoid b => WalkerT HermitEnv HermitM (Alt Id) b where
  crushT tt = altT (extractT tt) (\ _ _ r -> r)

instance WalkerL HermitEnv HermitM (Alt Id) where
  chooseL 0 = altT contextidT (\ con bs ce -> (ce, \ e1 -> pure (con,bs,e1))) `composeL` promoteL
  chooseL _ = failL

altT :: TranslateH (Expr Id) a1
     -> (AltCon -> [Id] -> a1 -> a)
     -> TranslateH (Alt Id) a
altT tt comp = translate $ \ c (con,bs,e) -> 
                comp con bs <$> apply tt (foldr addHermitEnvLambdaBinding c bs @@ 0) e

{-
-- Need to define thse
appR :: RewriteH (Expr Id) -> RewriteH (Expr Id) -> RewriteH (Expr Id)
appR r1 r2 = rewrite $ \ c e -> case e of
          App e1 e2 ->
                do e1' <- apply r1 c e1
                   e2' <- apply r2 c e2
                   return $ App e1' e2'
          _ -> fail "appR: not App"
-}

----------------------------------------------------------------
-- Bind

----------------------------------------------------------------
-- Need to write these for our entire grammar. These
-- are scoping aware combinators.

-- Expr
varT :: (Id -> a) -> TranslateH (Expr Id) a
varT comb = translate $ \ _ e -> case e of
        Var n -> pure (comb n)
        _     -> fail "no match for Var"

litT :: (Literal -> a) -> TranslateH (Expr Id) a
litT comb = translate $ \ _ e -> case e of
        Lit i -> pure (comb i)
        _     -> fail "no match for Lit"

appT :: TranslateH (Expr Id) a1
     -> TranslateH (Expr Id) a2
     -> (a1 -> a2 -> a)
     -> TranslateH (Expr Id) a
appT lhs rhs comp = translate $ \ c e -> case e of
        App e1 e2 -> comp <$> apply lhs (c @@ 0) e1 <*> apply rhs (c @@ 1) e2
        _         -> fail "no match for App"

lamT :: TranslateH (Expr Id) a1
     -> (Id -> a1 -> a)
     -> TranslateH (Expr Id) a
lamT tt comb = translate $ \ c e -> case e of
        Lam b e -> comb b <$> apply tt (addHermitEnvLambdaBinding b c @@ 0) e
        _       -> fail "no match for Lam"

letT :: TranslateH (Bind Id) a1
     -> TranslateH (Expr Id) a2
     -> (a1 -> a2 -> a)
     -> TranslateH (Expr Id) a
letT bdsT exprT comb = translate $ \ c e -> case e of
        Let bds e -> comb <$> apply bdsT (c @@ 0) bds <*> apply exprT (addHermitBinding bds c @@ 1) e
                -- use *original* env, because the bindings are self-binding,
                -- if they are recursive. See allR (Rec ...) for details.
        _         -> fail "no match for Let"

caseT :: TranslateH (Expr Id) a1
      -> (Int -> TranslateH (Alt Id) a2)          -- Int argument *starts* at 1.
      -> (a1 -> Id -> Type -> [a2] -> a)
      -> TranslateH (Expr Id) a
caseT exprT altT comb = translate $ \ c e -> case e of
        Case e b ty alts -> do
                e' <- apply exprT (c @@ 0) e
                let c' = addHermitBinding (NonRec b e) c
                alts' <- sequence [ apply (altT i) (c' @@ i) alt
                                  | (alt,i) <- zip alts [1..]
                                  ]
                pure (comb e' b ty alts')
        _ -> fail "no match for Case"

castT :: TranslateH (Expr Id) a1
     -> (a1 -> Coercion -> a)
     -> TranslateH (Expr Id) a
castT tt comb = translate $ \ c e -> case e of
        Cast e cast -> flip comb cast <$> apply tt (c @@ 0) e
        _           -> fail "no match for Cast"

tickT :: TranslateH (Expr Id) a1
     -> (Tickish Id -> a1 -> a)
     -> TranslateH (Expr Id) a
tickT tt comb = translate $ \ c e -> case e of
        Tick tk e -> comb tk <$> apply tt (c @@ 0) e
        _         -> fail "no match for Tick"

typeT :: (Type -> a) -> TranslateH (Expr Id) a
typeT comb = translate $ \ c e -> case e of
                                    Type i -> pure (comb i)
                                    _      -> fail "no match for Type"

coercionT :: (Coercion -> a) -> TranslateH (Expr Id) a
coercionT comb = translate $ \ c e -> case e of
                                        Coercion i -> pure (comb i)
                                        _          -> fail "no match for Coercion"

------------------------------------

consT :: TranslateH a a1
      -> TranslateH [a] a2
      -> (a1 -> a2 -> b)
      -> TranslateH [a] b
consT t1 t2 f = translate $ \ c e -> case e of
        (x:xs) -> f <$> apply t1 (c @@ 0) x <*> apply t2 (c @@ 1) xs
        _      -> fail "no match for consT"

nilT :: b -> TranslateH [a] b
nilT b = translate $ \ c e -> case e of
                                [] -> pure b
                                _  -> fail "no match for nilT"

------------------------------------
  
-- | pathT finds the current path.
pathT :: TranslateH a ContextPath
pathT = fmap hermitBindingPath contextT

---------------------------------------------------------------------
