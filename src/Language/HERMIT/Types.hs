{-# LANGUAGE TypeFamilies, FlexibleInstances, FlexibleContexts, GADTs #-}

module Language.HERMIT.Types where

import GhcPlugins
import qualified Data.Map as Map
import Data.Monoid

import Language.HERMIT.HermitEnv
import Language.HERMIT.HermitMonad
import Language.HERMIT.KURE

import qualified Control.Category as Cat
import Control.Arrow
import Control.Monad

----------------------------------------------------------------------------
{-
runHermitM :: HermitM a -> CoreM (Either String a)
runHermitM (HermitM m) = liftM Right m
runHermitM (FailM str) = return $ Left str
-}
----------------------------------------------------------------------------

---------------------------------------------------------------------

-- Lifting this out:
-- TODO: remove this, replace with Core everywhere.
-- Perhaps rename Blog to Generic :: *



-- To rename to Core
data Core
        = ModGutsCore   ModGuts
        | ProgramCore   CoreProgram
        | BindCore      (Bind Id)
        | ExprCore      (Expr Id)
--        | AltListCore   [Alt Id]
        | AltCore       (Alt Id)
        | TypeCore      Type


instance Term Core where
  type Generic Core = Core

  select   = Just
  inject   = id

  allR rr = rewrite $ \ (Context c blob) -> case blob of
          -- Going from Core to sub-Blog is the one case where you do not augment the path,
          -- but instead direct traffic.
          ModGutsCore modGuts -> liftM ModGutsCore $ apply (allR rr) (Context c modGuts)
          ProgramCore prog    -> liftM ProgramCore $ apply (allR rr) (Context c prog)
          BindCore    bind    -> liftM BindCore    $ apply (allR rr) (Context c bind)
          ExprCore    expr    -> liftM ExprCore    $ apply (allR rr) (Context c expr)
          AltCore     alt     -> liftM AltCore     $ apply (allR rr) (Context c alt)

  crushU tt = translate $ \ (Context c blob) -> case blob of
          ModGutsCore x -> apply (crushU tt) (Context c x)
          ProgramCore x -> apply (crushU tt) (Context c x)
          BindCore x    -> apply (crushU tt) (Context c x)
          ExprCore x    -> apply (crushU tt) (Context c x)
          AltCore x     -> apply (crushU tt) (Context c x)

  oneL n = translate $ \ (Context c blob) -> case blob of
          -- Going from Core to sub-Blog is the one case where you do not augment the path,
          -- but instead direct traffic.
          ModGutsCore x -> act (Context c x)
          ProgramCore x -> act (Context c x)
          BindCore x    -> act (Context c x)
          ExprCore x    -> act (Context c x)
          AltCore x     -> act (Context c x)

     where
               act :: (Term a, Generic a ~ Core)
                 => (Context a)
                 -> HermitM (Context (Generic a), Generic a -> HermitM Core)
               act cxt = do
                 (cb, fn) <- apply (oneL n) cxt
                 return $ (fmap inject cb, \ b -> case select b of
                                               Nothing -> fail "oneL failed"
                                               Just b -> liftM inject (fn b))

{-
          ProgramCore prog    -> liftM ProgramCore $ apply (allR rr) (Context c prog)
          BindCore    bind    -> liftM BindCore    $ apply (allR rr) (Context c bind)
          ExprCore    expr    -> liftM ExprCore    $ apply (allR rr) (Context c expr)
          AltCore     alt     -> liftM AltCore     $ apply (allR rr) (Context c alt)
-}
instance Term ModGuts where
  type Generic ModGuts = Core

  select (ModGutsCore guts) = return guts
  select _              = Nothing
  inject                = ModGutsCore

  allR rr = rewrite $ \ (Context c modGuts) -> do
          binds' <- apply (extractR rr) (Context (c @@ 0) (mg_binds modGuts))
          return (modGuts { mg_binds = binds' })

  crushU tt = modGutsT (extractU tt) $ \ _modGuts r -> r

  oneL 0 = modGutsT contextT (\ modGuts cxt -> (cxt, \ prog -> return $ modGuts { mg_binds = prog })) `glueL` promoteL
  oneL _ = failL "not lens for ModGuts"

modGutsT :: Translate CoreProgram a1
         -> (ModGuts -> a1 -> a)                -- slightly different; passes in *all* of the original
         -> Translate ModGuts a
modGutsT tt comp = translate $ \ (Context c modGuts) -> do
        p1' <- apply tt (Context (c @@ 0) (mg_binds modGuts))
        return $ comp modGuts p1'

instance Term CoreProgram where
  type Generic CoreProgram = Core

  select (ProgramCore guts) = return guts
  select _              = Nothing
  inject                = ProgramCore

  allR rr = rewrite $ \ (Context c prog) -> case prog of
          [] -> return []
          (bd:bds) -> do
              bd'  <- apply (extractR rr) (Context (c @@ 0) bd)
              let c' = addHermitBinding bd c
              bds' <- apply (extractR rr) (Context (c' @@ 1) bds)
              return $ bd' : bds'

  crushU tt = consBindT (extractU tt) (extractU tt) (\ x xs -> x `mappend` xs)
           <+ nilT mempty

  oneL 0 = consBindT contextT idR (\ cxt e2 -> (cxt, \ e1 -> return $ e1 : e2)) `glueL` promoteL
  oneL 1 = consBindT idR contextT (\ e1 cxt -> (cxt, \ e2 -> return $ e1 : e2)) `glueL` promoteL
  oneL _ = failL "no lens for CoreProgram"

consBindT :: (a ~ CoreBind)
      => Translate a a1
      -> Translate [a] a2
      -> (a1 -> a2 -> b)
      -> Translate [a] b
consBindT t1 t2 f = translate $ \ (Context c e) -> case e of
        (bd:bds) -> do
              r1 <- apply t1 (Context (c @@ 0) bd)
              let c' = addHermitBinding bd c
              r2 <- apply t2 (Context (c' @@ 1) bds)
              return $ f r1 r2
        _ -> fail "no match for consT"

instance Term (Bind Id) where
  type Generic (Bind Id) = Core

  select (BindCore expr) = return expr
  select _              = Nothing
  inject                = BindCore

  allR rr = rewrite $ \ (Context c e) -> case e of
          NonRec n e1 -> do
                   e1' <- apply (extractR rr) (Context (c @@ 0) e1)
                   return $ NonRec n e1'
          Rec bds -> do
                  -- Notice how we add the scoping bindings
                  -- here *before* decending into the rhss.
                   let env' = addHermitBinding (Rec bds) c
                   bds' <- sequence
                        [ do e' <- apply (extractR rr) (Context (env' @@ i) e)
                             return (n,e')
                        | ((n,e),i) <- zip bds [0..]
                        ]
                   return $ Rec bds'

  crushU tt = nonRecT (extractU tt) (\ _ r -> r)
           <+ recT    (const $ extractU tt) (mconcat . map snd)

  oneL n = case n of 0 -> nonrec <+ rec
                     n -> rec
     where
         nonrec = nonRecT contextT (\ v cxt -> (cxt, \ e -> return $ NonRec v e)) `glueL` promoteL
         rec    = do
            -- find the number of binds
            sz <- recT (const idR) length
            if n < 0 || n >= sz
                then failL "no lens for CoreBind"
                     -- if in range, then figure out context
                else recT (\ _ -> contextT)
                          (\ bds -> (snd (bds !! n)
                                    , \ e -> return $ Rec
                                                [ (v', if i == n then e else e')
                                                | ((v',Context _ e'),i) <- zip bds [0..]
                                                ]
                                    )
                          ) `glueL` promoteL

{-
  oneL 0 =
        <+ rec 0
  oneL n = rec n
    where
     rec n = recT idR contextT (\ e1 cxt -> (cxt, \ e2 -> return $ e1 : e2)) `glueL` promoteL
  oneL _ = failL
-}

recT :: (Int -> Translate CoreExpr a1)
      -> ([(Id,a1)] -> b)
      -> Translate CoreBind b
recT tt comp = translate $ \ (Context c e) -> case e of
        Rec bds -> do
          -- Notice how we add the scoping bindings
          -- here *before* decending into the rhss.
          let c' = addHermitBinding (Rec bds) c
          a1s <- sequence [ do rhs' <- apply (tt n) (Context (c' @@ n) rhs)
                               return (v,rhs')
                          | ((v,rhs),n) <- zip bds [0..]
                          ]
          return $ comp a1s
        _ -> fail "recT: not Rec"

nonRecT :: (Translate CoreExpr a1)
      -> (Var -> a1 -> b)
      -> Translate CoreBind b
nonRecT tt comp = translate $ \ (Context c e) -> case e of
        NonRec v e' -> do
                a1 <- apply tt (Context c e')
                return $ comp v a1
        _ -> fail "nonRecT: not NonRec"

instance Term (Expr Id) where
  type Generic (Expr Id) = Core

  select (ExprCore expr) = return expr
  select _              = Nothing
  inject                = ExprCore


  allR rr = rewrite $ \ (Context c e) -> case e of
          Var {} -> return e
          Lit {} -> return e
          App e1 e2 ->
                do e1' <- apply (extractR rr) (Context (c @@ 0) e1)
                   e2' <- apply (extractR rr) (Context (c @@ 1) e2)
                   return $ App e1' e2'
          Lam b e ->
                do e' <- apply (extractR rr) (Context (addHermitEnvLambdaBinding b c @@ 0) e)
                   return $ Lam b e'
          Let bds e ->
                do
                   -- use *original* env, because the bindings are self-binding,
                   -- if they are recursive. See allR (Rec ...) for details.
                   bds' <- apply (extractR rr) (Context (c @@ 0) bds)
                   let c' = addHermitBinding bds c
                   e'   <- apply (extractR rr) (Context (c' @@ 1) e)
                   return $ Let bds' e'
          Case e b ty alts ->
                do e' <- apply (extractR rr) (Context (c @@ 0) e)
                   let c' = addHermitBinding (NonRec b e) c
                   alts' <-
                        sequence [ apply (extractR rr) (Context (c' @@ i) alt)
                                 | (alt,i) <- zip alts [1..]
                                 ]
                   return $ Case e b ty alts'

          Cast e cast ->
                do e' <- apply (extractR rr) (Context (c @@ 0) e)
                   return $ Cast e' cast
          Tick tk e ->
                do e' <- apply (extractR rr) (Context (c @@ 0) e)
                   return $ Tick tk e'
                -- Not sure about this. Should be descend into the type here?
                -- If we do so, we should also descend into the types
                -- inside Coercion, Id, etc.
          Type _ty -> return $ e
          Coercion _c -> return $ e

  crushU tt = varT (\ _ -> mempty)
           <+ litT (\ _ -> mempty)
           <+ appT (extractU tt) (extractU tt) mappend
           <+ lamT (extractU tt) (\ _ r -> r)
           <+ letT (extractU tt) (extractU tt) mappend
           <+ caseT (extractU tt) (const $ extractU tt) (\ r v t rs -> mconcat (r : rs))
           <+ castT (extractU tt) (\ r _ -> r)
           <+ tickT (extractU tt) (\ _ r -> r)
           <+ typeT (\ _ -> mempty)
           <+ coercionT (\ _ -> mempty)

  oneL n = case n of
      0 -> (( appT contextT idR  $ \ cxt e2       -> (cxt, \ e1 -> return $ App e1 e2) )        `glueL` promoteL )
        <+ (( lamT contextT      $ \ v cxt        -> (cxt, \ e1 -> return $ Lam v e1) )         `glueL` promoteL )
        <+ (( letT contextT idR  $ \ cxt e2       -> (cxt, \ bd -> return $ Let bd e2) )        `glueL` promoteL )
        <+ (( caseT contextT (const idR)
                                 $ \ cxt v t alts -> (cxt, \ e1 -> return $ Case e1 v t alts) ) `glueL` promoteL )
        <+ (( castT contextT     $ \ cxt c        -> (cxt, \ e1 -> return $ Cast e1 c) )        `glueL` promoteL )
        <+ (( tickT contextT     $ \ t cxt        -> (cxt, \ e1 -> return $ Tick t e1) )        `glueL` promoteL )
      1 -> (( appT idR contextT  $ \ e1 cxt       -> (cxt, \ e2 -> return $ App e1 e2) )        `glueL` promoteL )
        <+ (( letT idR contextT  $ \ bd cxt       -> (cxt, \ e2 -> return $ Let bd e2) )        `glueL` promoteL )
        <+ caseOneL
      n -> caseOneL
    where
        caseOneL = do
            sz <- caseT idR (const idR) $ \ _ _ _ alts -> length alts
            if n < 1 || n > sz
                then failL "no lens for Expr"
                else caseT idR (const contextT)
                               (\ e v t alts -> ( alts !! (n - 1)
                                                  , \ alt -> return $ Case e v t
                                                              [ if i == n then alt else alt'
                                                              | ((Context _ alt'),i) <- zip alts [1..]
                                                              ]
                                                  )
                               ) `glueL` promoteL

--        <+ (( caseT contextT idR $ \ cxt v t alts -> (cxt, \ e1 -> return $ Case e1 v t alts) ) `glueL` promoteL )

--         foo cxt $ \ e1 -> App e1 e2 )

foo :: (Monad m, Term a, Term exp)
     => Context a -> (exp -> a1) -> (Context (Generic a), Generic exp -> m a1)
foo cxt f =
             ( fmap inject cxt
              , \ e -> case select e of
                         Nothing -> fail ""
                         Just e1 -> return (f e1)
              )

{-
instance Term [Alt Id] where
  type Generic [Alt Id] = Core

  select (AltListCore expr) = return expr
  select _              = Nothing
  inject                = AltListCore

  allR rr = ( consT (extractR rr) (extractR rr) $ \ x xs -> x : xs )
         <+ ( nilT                              $ [] )

  crushU tt = ( consT (extractU tt) (extractU tt) $ mappend )
           <+ ( nilT                              $ mempty )

  crushU tt = ( consT (extractU tt) (extractU tt) $ mappend )
           <+ ( nilT                              $ mempty )

  oneL 0 = consT contextT idR  (\ cxt e2 -> (cxt, \ e1 -> return $ e1 : e2) )        `glueL` promoteL
  oneL 1 = consT idR contextT  (\ e1 cxt -> (cxt, \ e2 -> return $ e1 : e2) )        `glueL` promoteL
  oneL _ = failL
-}

instance Term (Alt Id) where
  type Generic (Alt Id) = Core

  select (AltCore expr) = return expr
  select _              = Nothing
  inject                = AltCore

  allR rr = rewrite $ \ (Context c (con,bs,e)) -> do
                        let c' = foldr addHermitEnvLambdaBinding c bs
                        e' <- apply (extractR rr) (Context (c' @@ 0) e)
                        return (con,bs,e')

  crushU tt = altT (extractU tt) $ \ con bs r -> r

  oneL 0 = altT contextT (\ con bs cxt -> (cxt, \ e1 -> return $ (con,bs,e1))) `glueL` promoteL
  oneL _ = failL "no lens for Alt"

altT :: Translate (Expr Id) a1
     -> (AltCon -> [Id] -> a1 -> a)
     -> Translate (Alt Id) a
altT tt comp = translate $ \ (Context c e) -> case e of
     (con,bs,e) -> do
        let c' = foldr addHermitEnvLambdaBinding c bs
        e' <- apply tt (Context (c' @@ 0) e)
        return $ comp con bs e'
{-
-- Need to define thse
appR :: Rewrite (Expr Id) -> Rewrite (Expr Id) -> Rewrite (Expr Id)
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
varT :: (Id -> a)
     -> Translate (Expr Id) a
varT comb = translate $ \ (Context c e) -> case e of
        Var n -> return $ comb n
        _ -> fail "no match for Var"

litT :: (Literal -> a)
     -> Translate (Expr Id) a
litT comb = translate $ \ (Context c e) -> case e of
        Lit i -> return $ comb i
        _ -> fail "no match for Lit"

appT :: Translate (Expr Id) a1
     -> Translate (Expr Id) a2
     -> (a1 -> a2 -> a)
     -> Translate (Expr Id) a
appT lhs rhs comp = translate $ \ (Context c e) -> case e of
        App e1 e2 -> do
                e1' <- apply lhs (Context (c @@ 0) e1)
                e2' <- apply rhs (Context (c @@ 1) e2)
                return $ comp e1' e2'
        _ -> fail "no match for App"

lamT :: Translate (Expr Id) a1
     -> (Id -> a1 -> a)
     -> Translate (Expr Id) a
lamT tt comb = translate $ \ (Context c e) -> case e of
        Lam b e -> do
                e' <- apply tt (Context (addHermitEnvLambdaBinding b c @@ 0) e)
                return $ comb b e'
        _ -> fail "no match for Lam"

letT :: Translate (Bind Id) a1
     -> Translate (Expr Id) a2
     -> (a1 -> a2 -> a)
     -> Translate (Expr Id) a
letT bdsT exprT comb = translate $ \ (Context c e) -> case e of
        Let bds e -> do
                -- use *original* env, because the bindings are self-binding,
                -- if they are recursive. See allR (Rec ...) for details.
                bds' <- apply bdsT (Context (c @@ 0) bds)
                let c' = addHermitBinding bds c
                e'   <- apply exprT (Context (c' @@ 1) e)
                return $ comb bds' e'
        _ -> fail "no match for Let"

caseT :: Translate (Expr Id) a1
      -> (Int -> Translate (Alt Id) a2)          -- Int argument *starts* at 1.
      -> (a1 -> Id -> Type -> [a2] -> a)
      -> Translate (Expr Id) a
caseT exprT altT comb = translate $ \ (Context c e) -> case e of
        Case e b ty alts -> do
                e' <- apply exprT (Context (c @@ 0) e)
                let c' = addHermitBinding (NonRec b e) c
                alts' <- sequence [ apply (altT i) (Context (c' @@ i) alt)
                                  | (alt,i) <- zip alts [1..]
                                  ]
                return $ comb e' b ty alts'
        _ -> fail "no match for Case"

castT :: Translate (Expr Id) a1
     -> (a1 -> Coercion -> a)
     -> Translate (Expr Id) a
castT tt comb = translate $ \ (Context c e) -> case e of
        Cast e cast -> do
                e' <- apply tt (Context (c @@ 0) e)
                return $ comb e' cast
        _ -> fail "no match for Cast"

tickT :: Translate (Expr Id) a1
     -> (Tickish Id -> a1 -> a)
     -> Translate (Expr Id) a
tickT tt comb = translate $ \ (Context c e) -> case e of
        Tick tk e -> do
                e' <- apply tt (Context (c @@ 0) e)
                return $ comb tk e'
        _ -> fail "no match for Tick"

typeT :: (Type -> a)
     -> Translate (Expr Id) a
typeT comb = translate $ \ (Context c e) -> case e of
        Type i -> return $ comb i
        _ -> fail "no match for Type"

coercionT :: (Coercion -> a)
     -> Translate (Expr Id) a
coercionT comb = translate $ \ (Context c e) -> case e of
        Coercion i -> return $ comb i
        _ -> fail "no match for Coercion"

------------------------------------

consT :: Translate a a1
      -> Translate [a] a2
      -> (a1 -> a2 -> b)
      -> Translate [a] b
consT t1 t2 f = translate $ \ (Context c e) -> case e of
        (x:xs) -> do
                r1 <- apply t1 (Context (c @@ 0) x)
                r2 <- apply t2 (Context (c @@ 1) xs)
                return $ f r1 r2
        _ -> fail "no match for consT"

nilT :: b
     -> Translate [a] b
nilT b = translate $ \ (Context c e) -> case e of
        [] -> return b
        _ -> fail "no match for nilT"

------------------------------------
-- | pathT finds the current path.
pathT :: Translate a ContextPath
pathT = fmap (\ (Context c _) -> hermitBindingPath c) contextT

---------------------------------------------------------------------
