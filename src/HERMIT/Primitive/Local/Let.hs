{-# LANGUAGE FlexibleContexts, ScopedTypeVariables #-}

module HERMIT.Primitive.Local.Let
       ( -- * Rewrites on Let Expressions
         externals
         -- ** Let Elimination
       , letSubstR
       , safeLetSubstR
       , letElim
       , letNonRecElim
       , letRecElim
         -- ** Let Introduction
       , letIntro
         -- ** Let Floating
       , letFloatApp
       , letFloatArg
       , letFloatLet
       , letFloatLam
       , letFloatCase
       , letFloatCast
       , letFloatExpr
       , letFloatLetTop
         -- ** Let Unfloating
       , letUnfloat
       , letUnfloatApp
       , letUnfloatCase
       , letUnfloatLam
         -- ** Miscallaneous
       , reorderNonRecLets
       , letTupleR
       , letToCase
       )
where

import GhcPlugins

import Control.Arrow
import Control.Monad

import Data.List
import Data.Monoid

import HERMIT.Core
import HERMIT.Context
import HERMIT.Monad
import HERMIT.Kure
import HERMIT.External
import HERMIT.GHC

import HERMIT.Primitive.Common
import HERMIT.Primitive.GHC hiding (externals)
import HERMIT.Primitive.AlphaConversion hiding (externals)

import HERMIT.Primitive.Local.Bind hiding (externals)

import qualified Language.Haskell.TH as TH

------------------------------------------------------------------------------

-- | Externals relating to 'Let' expressions.
externals :: [External]
externals =
    [ external "let-subst" (promoteExprR letSubstR :: RewriteH Core)
        [ "Let substitution: (let x = e1 in e2) ==> (e2[e1/x])"
        , "x must not be free in e1." ]                                         .+ Deep .+ Eval
    , external "safe-let-subst" (promoteExprR safeLetSubstR :: RewriteH Core)
        [ "Safe let substitution"
        , "let x = e1 in e2, safe to inline without duplicating work ==> e2[e1/x],"
        , "x must not be free in e1." ]                                         .+ Deep .+ Eval .+ Bash
    -- , external "safe-let-subst-plus" (promoteExprR safeLetSubstPlusR :: RewriteH Core)
    --     [ "Safe let substitution"
    --     , "let { x = e1, ... } in e2, "
    --     , "  where safe to inline without duplicating work ==> e2[e1/x,...],"
    --     , "only matches non-recursive lets" ]  .+ Deep .+ Eval
    , external "let-intro" (promoteExprR . letIntro . show :: TH.Name -> RewriteH Core)
        [ "e => (let v = e in v), name of v is provided" ]                      .+ Shallow .+ Introduce
    , external "let-elim" (promoteExprR letElim :: RewriteH Core)
        [ "Remove an unused let binding."
        , "(let v = e1 in e2) ==> e2, if v is not free in e1 or e2." ]          .+ Eval .+ Shallow .+ Bash
--    , external "let-constructor-reuse" (promoteR $ not_defined "constructor-reuse" :: RewriteH Core)
--        [ "let v = C v1..vn in ... C v1..vn ... ==> let v = C v1..vn in ... v ..., fails otherwise" ] .+ Eval
    , external "let-float-app" (promoteExprR letFloatApp :: RewriteH Core)
        [ "(let v = ev in e) x ==> let v = ev in e x" ]                         .+ Commute .+ Shallow .+ Bash
    , external "let-float-arg" (promoteExprR letFloatArg :: RewriteH Core)
        [ "f (let v = ev in e) ==> let v = ev in f e" ]                         .+ Commute .+ Shallow .+ Bash
    , external "let-float-lam" (promoteExprR letFloatLam :: RewriteH Core)
        [ "(\\ v1 -> let v2 = e1 in e2)  ==>  let v2 = e1 in (\\ v1 -> e2), if v1 is not free in e2."
        , "If v1 = v2 then v1 will be alpha-renamed." ]                         .+ Commute .+ Shallow .+ Bash
    , external "let-float-let" (promoteExprR letFloatLet :: RewriteH Core)
        [ "let v = (let w = ew in ev) in e ==> let w = ew in let v = ev in e" ] .+ Commute .+ Shallow .+ Bash
    , external "let-float-case" (promoteExprR letFloatCase :: RewriteH Core)
        [ "case (let v = ev in e) of ... ==> let v = ev in case e of ..." ]     .+ Commute .+ Shallow .+ Eval .+ Bash
    , external "let-float-cast" (promoteExprR letFloatCast :: RewriteH Core)
        [ "cast (let bnds in e) co ==> let bnds in cast e co" ]                 .+ Commute .+ Shallow .+ Bash
    , external "let-float-top" (promoteProgR letFloatLetTop :: RewriteH Core)
        [ "v = (let w = ew in ev) : bds ==> w = ew : v = ev : bds" ]            .+ Commute .+ Shallow .+ Bash
    , external "let-float" (promoteProgR letFloatLetTop <+ promoteExprR letFloatExpr :: RewriteH Core)
        [ "Float a Let whatever the context." ]                                 .+ Commute .+ Shallow  -- Don't include in bash, as each sub-rewrite is tagged "Bash" already.
    , external "let-to-case" (promoteExprR letToCase :: RewriteH Core)
        [ "let v = ev in e ==> case ev of v -> e" ]                             .+ Commute .+ Shallow .+ PreCondition
--    , external "let-to-case-unbox" (promoteR $ not_defined "let-to-case-unbox" :: RewriteH Core)
--        [ "let v = ev in e ==> case ev of C v1..vn -> let v = C v1..vn in e" ]
    , external "let-unfloat" (promoteExprR letUnfloat :: RewriteH Core)
        [ "Unfloat a let if possible." ]                                        .+ Commute .+ Shallow
    , external "let-unfloat-app" ((promoteExprR letUnfloatApp >+> anybuR (promoteExprR letElim)) :: RewriteH Core)
        [ "let v = ev in f a ==> (let v = ev in f) (let v = ev in a)" ]         .+ Commute .+ Shallow
    , external "let-unfloat-case" ((promoteExprR letUnfloatCase >+> anybuR (promoteExprR letElim)) :: RewriteH Core)
        [ "let v = ev in case s of p -> e ==> case (let v = ev in s) of p -> let v = ev in e"
        , "if v does not shadow a pattern binder in p" ]                        .+ Commute .+ Shallow
    , external "let-unfloat-lam" ((promoteExprR letUnfloatLam >+> anybuR (promoteExprR letElim)) :: RewriteH Core)
        [ "let v = ev in \\ x -> e ==> \\ x -> let v = ev in e"
        , "if v does not shadow x" ]                                            .+ Commute .+ Shallow
    , external "reorder-lets" (promoteExprR . reorderNonRecLets :: [TH.Name] -> RewriteH Core)
        [ "Re-order a sequence of nested non-recursive let bindings."
        , "The argument list should contain the let-bound variables, in the desired order." ]
    , external "let-tuple" (promoteExprR . letTupleR . show :: TH.Name -> RewriteH Core)
        [ "Combine nested non-recursive lets into case of a tuple."
        , "E.g. let {v1 = e1 ; v2 = e2 ; v3 = e3} in body ==> case (e1,e2,e3) of {(v1,v2,v3) -> body}" ] .+ Commute
    ]

-------------------------------------------------------------------------------------------

-- | (let x = e1 in e2) ==> (e2[e1/x]), (x must not be free in e1)
letSubstR :: (AddBindings c, ExtendPath c Crumb, MonadCatch m) => Rewrite c m CoreExpr
letSubstR =  prefixFailMsg "Let substition failed: " $
             withPatFailMsg ("expression is not a non-recursive let binding.") $
             do Let (NonRec v rhs) body <- letAllR (tryR recToNonrecR) idR
                contextonlyT $ \ c -> apply (substExprR v rhs) c body

-- | This is quite expensive (O(n) for the size of the sub-tree).
safeLetSubstR :: forall c m. (AddBindings c, ExtendPath c Crumb, ReadBindings c, MonadCatch m) => Rewrite c m CoreExpr
safeLetSubstR =  prefixFailMsg "Safe let-substition failed: " $
                 withPatFailMsg ("expression is not a non-recursive let binding.") $
                 do e@(Let (NonRec v rhs) body) <- letAllR (tryR recToNonrecR) idR

                    guardMsg (not $ isCoVar v) "We consider it unsafe to substitute let-bound coercions.  I'm not sure why we think this." -- TODO

                    safeSubstId <- letNonRecT mempty safeBindT (occursSafeToLetSubstId v) (\ () -> (||)) <<< return e
                    when (isId v) (guardMsg safeSubstId "safety criteria not met.")

                    -- By (our) definition, types are a trivial bind.

                    contextonlyT $ \ c -> apply (substExprR v rhs) c body

  where
    -- what about other Expr constructors?
    safeBindT :: Translate c m CoreExpr Bool
    safeBindT =
      do c <- contextT
         arr $ \ e ->
           case e of
             Var {} -> True
             Lam {} -> True
             App {} -> case collectArgs e of
                         (Var f,args) -> arityOf c f > length (filter (not . isTyCoArg) args) -- Neil: I've changed this to "not . isTyCoArg" rather than "not . isTypeArg".  This may not be the right thing to do though.
                         (other,args) -> case collectBinders other of
                                           (bds,_) -> length bds > length args
             _      -> False

    occursSafeToLetSubstId :: Id -> Translate c m CoreExpr Bool
    occursSafeToLetSubstId i =
      do depth <- varBindingDepthT i
         let occursHereT :: Translate c m Core ()
             occursHereT = promoteExprT (exprIsOccurrenceOfT i depth >>> guardT)

             -- lamOccurrenceT can only fail if the expression is not a Lam
             -- return either 2 (occurrence) or 0 (no occurrence)
             lamOccurrenceT :: Translate c m CoreExpr (Sum Int)
             lamOccurrenceT =  lamT mempty
                                    (mtryM (Sum 2 <$ extractT (onetdT occursHereT)))
                                    mappend

             occurrencesT :: Translate c m Core (Sum Int)
             occurrencesT = prunetdT (promoteExprT lamOccurrenceT <+ (Sum 1 <$ occursHereT))

         extractT occurrencesT >>^ (getSum >>> (< 2))

(<$) :: Monad m => a -> m b -> m a
a <$ mb = mb >> return a


-- This could be simply "repeatR safeLetSubst" I think?
--  'safeLetSubstPlusR' tries to inline a stack of bindings, stopping when reaches
-- the end of the stack of lets.
-- safeLetSubstPlusR :: (ExtendPath c Crumb, AddBindings c, ReadBindings c, MonadCatch m) => Rewrite c m CoreExpr
-- safeLetSubstPlusR = tryR (letT idR safeLetSubstPlusR Let) >>> safeLetSubstR

-------------------------------------------------------------------------------------------

-- | @e@ ==> @(let v = e in v)@, name of v is provided
letIntro :: String -> Rewrite c HermitM CoreExpr
letIntro nm = prefixFailMsg "Let-introduction failed: " $
              contextfreeT $ \ e -> do guardMsg (not $ isTypeArg e) "let expressions may not return a type."
                                       v <- newIdH nm (exprKindOrType e)
                                       return $ Let (NonRec v e) (Var v)

letElim :: (ExtendPath c Crumb, AddBindings c, MonadCatch m) => Rewrite c m CoreExpr
letElim = prefixFailMsg "Dead-let-elimination failed: " $
          withPatFailMsg (wrongExprForm "Let binds expr") $
          do Let bg _ <- idR
             case bg of
               NonRec{} -> letNonRecElim
               Rec{}    -> letRecElim

-- | Remove an unused non-recursive let binding.
--   @let v = E1 in E2@ ==> @E2@, if @v@ is not free in @E2@
letNonRecElim :: MonadCatch m => Rewrite c m CoreExpr
letNonRecElim = withPatFailMsg (wrongExprForm "Let (NonRec v e1) e2") $
                do Let (NonRec v _) e <- idR
                   guardMsg (v `notElemVarSet` exprFreeVars e) "let-bound variable appears in the expression."
                   return e

-- TODO: find the GHC way to do this, as this implementation will be defeated by mutual recursion
-- | Remove all unused recursive let bindings in the current group.
letRecElim :: (ExtendPath c Crumb, AddBindings c, MonadCatch m) => Rewrite c m CoreExpr
letRecElim = withPatFailMsg (wrongExprForm "Let (Rec v e1) e2") $
 do Let (Rec bnds) body <- idR
    (vsAndFrees, bodyFrees) <- letRecDefT (\ _ -> (idR,exprFreeVarsT)) exprFreeVarsT (,)
    -- binder is alive if it is found free anywhere but its own rhs
    let living = [ v
                 | (v,_) <- vsAndFrees
                 , v `elemVarSet` bodyFrees || v `elemVarSet` unionVarSets [ fs | (v',fs) <- vsAndFrees, v' /= v ]
                 ]
    if null living
        then return body
        else if length living == length bnds
                then fail "no dead code."
                else return $ Let (Rec [ (v,rhs) | (v,rhs) <- bnds, v `elem` living ]) body

-- | @let v = ev in e@ ==> @case ev of v -> e@
letToCase :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
letToCase = prefixFailMsg "Converting Let to Case failed: " $
            withPatFailMsg (wrongExprForm "Let (NonRec v e1) e2") $
  do Let (NonRec v ev) _ <- idR
     guardMsg (not $ isTyCoArg ev) "cannot case on a type or coercion."
     nameModifier <- freshNameGenT Nothing
     caseBndr <- constT (cloneVarH nameModifier v)
     letT mempty (replaceVarR v caseBndr) $ \ () e' -> Case ev caseBndr (varType v) [(DEFAULT, [], e')]

-------------------------------------------------------------------------------------------

-- | @(let v = ev in e) x@ ==> @let v = ev in e x@
letFloatApp :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
letFloatApp = prefixFailMsg "Let floating from App function failed: " $
  do vs <- appT (liftM mkVarSet letVarsT) exprFreeVarsT intersectVarSet
     let letAction = if isEmptyVarSet vs then idR else alphaLet
     appT letAction idR $ \ (Let bnds e) x -> Let bnds $ App e x

-- | @f (let v = ev in e)@ ==> @let v = ev in f e@
letFloatArg :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
letFloatArg = prefixFailMsg "Let floating from App argument failed: " $
  do vs <- appT exprFreeVarsT (liftM mkVarSet letVarsT) intersectVarSet
     let letAction = if isEmptyVarSet vs then idR else alphaLet
     appT idR letAction $ \ f (Let bnds e) -> Let bnds $ App f e

-- | @let v = (let w = ew in ev) in e@ ==> @let w = ew in let v = ev in e@
letFloatLet :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
letFloatLet = prefixFailMsg "Let floating from Let failed: " $
  do vs <- letNonRecT mempty (liftM mkVarSet letVarsT) exprFreeVarsT (\ () -> intersectVarSet)
     let bdsAction = if isEmptyVarSet vs then idR else nonRecAllR idR alphaLet
     letT bdsAction idR $ \ (NonRec v (Let bds ev)) e -> Let bds $ Let (NonRec v ev) e

-- | @(\ v1 -> let v2 = e1 in e2)@  ==>  @let v2 = e1 in (\ v1 -> e2)@
--   Fails if @v1@ occurs in @e1@.
--   If @v1@ = @v2@ then @v1@ will be alpha-renamed.
letFloatLam :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
letFloatLam = prefixFailMsg "Let floating from Lam failed: " $
              withPatFailMsg (wrongExprForm "Lam v1 (Let (NonRec v2 e1) e2)") $
  do Lam v1 (Let (NonRec v2 e1) e2) <- idR
     guardMsg (v1 `notElemVarSet` exprFreeVars e1) $ var2String v1 ++ " occurs in the definition of " ++ var2String v2 ++ "."
     if v1 == v2
      then alphaLam Nothing >>> letFloatLam
      else return (Let (NonRec v2 e1) (Lam v1 e2))

-- | @case (let bnds in e) of wild alts@ ==> @let bnds in (case e of wild alts)@
--   Fails if any variables bound in @bnds@ occurs in @alts@.
letFloatCase :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
letFloatCase = prefixFailMsg "Let floating from Case failed: " $
  do captures <- caseT letVarsT
                       idR
                       idR
                       (\ _ -> altFreeVarsExclWildT)
                       (\ vs wild _ fs -> mkVarSet vs `intersectVarSet` unionVarSets (map ($ wild) fs))
     caseT (if isEmptyVarSet captures then idR else alphaLetVars $ varSetElems captures)
           idR
           idR
           (const idR)
           (\ (Let bnds e) wild ty alts -> Let bnds (Case e wild ty alts))

-- | @cast (let bnds in e) co@ ==> @let bnds in cast e co@
letFloatCast :: MonadCatch m => Rewrite c m CoreExpr
letFloatCast = prefixFailMsg "Let floating from Cast failed: " $
               withPatFailMsg (wrongExprForm "Cast (Let bnds e) co") $
  do Cast (Let bnds e) co <- idR
     return (Let bnds (Cast e co))

-- | Float a 'Let' through an expression, whatever the context.
letFloatExpr :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
letFloatExpr = setFailMsg "Unsuitable expression for Let floating." $
               letFloatArg <+ letFloatApp <+ letFloatLet <+ letFloatLam <+ letFloatCase <+ letFloatCast

-- | @'ProgCons' ('NonRec' v ('Let' ('NonRec' w ew) ev)) p@ ==> @'ProgCons' ('NonRec' w ew) ('ProgCons' ('NonRec' v ev) p)@
letFloatLetTop :: (ExtendPath c Crumb, AddBindings c, MonadCatch m) => Rewrite c m CoreProg
letFloatLetTop = prefixFailMsg "Let floating to top level failed: " $
                 withPatFailMsg (wrongExprForm "NonRec v (Let (NonRec w ew) ev) `ProgCons` p") $
  do NonRec v (Let (NonRec w ew) ev) `ProgCons` p <- idR
     guardMsg (not $ isTyCoArg ew) "type and coercion bindings are not allowed at the top level."
     return (NonRec w ew `ProgCons` NonRec v ev `ProgCons` p)

-------------------------------------------------------------------------------------------

-- | Unfloat a 'Let' if possible.
letUnfloat :: (ExtendPath c Crumb, AddBindings c, MonadCatch m) => Rewrite c m CoreExpr
letUnfloat = letUnfloatCase <+ letUnfloatApp <+ letUnfloatLam

-- | @let v = ev in case s of p -> e@ ==> @case (let v = ev in s) of p -> let v = ev in e@,
--   if @v@ does not shadow a pattern binder in @p@
letUnfloatCase :: (ExtendPath c Crumb, AddBindings c, MonadCatch m) => Rewrite c m CoreExpr
letUnfloatCase = prefixFailMsg "Let unfloating from case failed: " $
                 withPatFailMsg (wrongExprForm "Let bnds (Case s w ty alts)") $
  do Let bnds (Case s w ty alts) <- idR
     captured <- letT bindVarsT caseVarsT intersect
     guardMsg (null captured) "let bindings would capture case pattern bindings."
     unbound <- letT bindVarsT (caseT mempty mempty tyVarsOfTypeT (const mempty) $ \ () () vs (_::[()]) -> varSetElems vs) intersect
     guardMsg (null unbound) "type variables in case signature would become unbound."
     return $ Case (Let bnds s) w ty $ mapAlts (Let bnds) alts

-- | @let v = ev in f a@ ==> @(let v = ev in f) (let v = ev in a)@
letUnfloatApp :: MonadCatch m => Rewrite c m CoreExpr
letUnfloatApp = prefixFailMsg "Let unfloating from app failed: " $
                withPatFailMsg (wrongExprForm "Let bnds (App e1 e2)") $
  do Let bnds (App e1 e2) <- idR
     return $ App (Let bnds e1) (Let bnds e2)

-- | @let v = ev in \ x -> e@ ==> @\x -> let v = ev in e@
--   if @v@ does not shadow @x@
letUnfloatLam :: (ExtendPath c Crumb, AddBindings c, MonadCatch m) => Rewrite c m CoreExpr
letUnfloatLam = prefixFailMsg "Let unfloating from lambda failed: " $
                withPatFailMsg (wrongExprForm "Let bnds (Lam v e)") $
  do Let bnds (Lam v e) <- idR
     safe <- letT bindVarsT lamVarT $ flip notElem
     guardMsg safe "let bindings would capture lambda binding."
     return $ Lam v $ Let bnds e

-------------------------------------------------------------------------------------------

-- | Re-order a sequence of nested non-recursive let bindings.
--   The argument list should contain the let-bound variables, in the desired order.
reorderNonRecLets :: MonadCatch m => [TH.Name] -> Rewrite c m CoreExpr
reorderNonRecLets nms = prefixFailMsg "Reorder lets failed: " $
                 do guardMsg (not $ null nms) "no names given."
                    guardMsg (nodups nms) "duplicate names given."
                    e <- idR
                    (ves,x) <- setFailMsg "insufficient non-recursive lets." $ takeNonRecLets (length nms) e
                    guardMsg (noneFreeIn ves) "some of the bound variables appear in the right-hand-sides."
                    e' <- mkNonRecLets `liftM` mapM (lookupName ves) nms `ap` return x
                    guardMsg (not $ exprEqual e e') "bindings already in specified order."
                    return e'

  where
    takeNonRecLets :: Monad m => Int -> CoreExpr -> m ([(Var,CoreExpr)],CoreExpr)
    takeNonRecLets 0 x                      = return ([],x)
    takeNonRecLets n (Let (NonRec v1 e1) x) = first ((v1,e1):) `liftM` takeNonRecLets (n-1) x
    takeNonRecLets _ _                      = fail "insufficient non-recursive lets."

    noneFreeIn :: [(Var,CoreExpr)] -> Bool
    noneFreeIn ves = let (vs,es) = unzip ves
                      in all (`notElemVarSet` unionVarSets (map exprFreeVars es)) vs

    lookupName :: Monad m => [(Var,CoreExpr)] -> TH.Name -> m (Var,CoreExpr)
    lookupName ves nm = let n = show nm
                         in case filter (cmpString2Var n . fst) ves of
                              []   -> fail $ "name " ++ n ++ " not matched."
                              [ve] -> return ve
                              _    -> fail $ "multiple matches for " ++ n ++ "."

    mkNonRecLets :: [(Var,CoreExpr)] -> CoreExpr -> CoreExpr
    mkNonRecLets []          x  = x
    mkNonRecLets ((v,e):ves) x  = Let (NonRec v e) (mkNonRecLets ves x)

-------------------------------------------------------------------------------------------

-- | Combine nested non-recursive lets into case of a tuple.
--   E.g. let {v1 = e1 ; v2 = e2 ; v3 = e3} in body ==> case (e1,e2,e3) of {(v1,v2,v3) -> body}
letTupleR :: String -> Rewrite c HermitM CoreExpr
letTupleR nm = prefixFailMsg "Let-tuple failed: " $
      do (bnds, body) <- arr collectLets
         let numBnds = length bnds
         guardMsg (numBnds > 1) "at least two non-recursive let bindings of identifiers required."

         let (vs, rhss) = unzip bnds

         -- check if tupling the bindings would cause unbound variables
         let frees  = map exprFreeVars (drop 1 rhss)
             used   = unionVarSets $ zipWith intersectVarSet (map (mkVarSet . (`take` vs)) [1..]) frees
         if isEmptyVarSet used
           then let rhs = mkCoreTup rhss
                in constT $ do wild <- newIdH nm (exprType rhs)
                               return $ mkSmallTupleCase vs body wild rhs

           else fail $ "the following bound variables are used in subsequent bindings: " ++ showVarSet used

  where
    -- we only collect identifiers (not type or coercion vars) because we intend to case on them.
    collectLets :: CoreExpr -> ([(Id, CoreExpr)],CoreExpr)
    collectLets (Let (NonRec v e) body) | isId v = first ((v,e):) (collectLets body)
    collectLets expr                             = ([],expr)

-------------------------------------------------------------------------------------------
