{-# LANGUAGE FlexibleContexts, ScopedTypeVariables #-}

module HERMIT.Primitive.Local.Let
       ( -- * Rewrites on Let Expressions
         externals
         -- ** Let Elimination
       , letSubstR
       , safeLetSubstR
       , letElimR
       , letNonRecElimR
       , letRecElimR
         -- ** Let Introduction
       , letIntroR
         -- ** Let Floating
       , letFloatAppR
       , letFloatArgR
       , letFloatLetR
       , letFloatLamR
       , letFloatCaseR
       , letFloatCastR
       , letFloatExprR
       , letFloatTopR
         -- ** Let Unfloating
       , letUnfloatR
       , letUnfloatAppR
       , letUnfloatCaseR
       , letUnfloatLamR
         -- ** Miscallaneous
       , reorderNonRecLetsR
       , letTupleR
       , letToCaseR
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
import HERMIT.Utilities

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
        , "x must not be free in e1." ]                                         .+ Deep .+ Eval
    -- , external "safe-let-subst-plus" (promoteExprR safeLetSubstPlusR :: RewriteH Core)
    --     [ "Safe let substitution"
    --     , "let { x = e1, ... } in e2, "
    --     , "  where safe to inline without duplicating work ==> e2[e1/x,...],"
    --     , "only matches non-recursive lets" ]  .+ Deep .+ Eval
    , external "let-intro" (promoteExprR . letIntroR . show :: TH.Name -> RewriteH Core)
        [ "e => (let v = e in v), name of v is provided" ]                      .+ Shallow .+ Introduce
    , external "let-elim" (promoteExprR letElimR :: RewriteH Core)
        [ "Remove an unused let binding."
        , "(let v = e1 in e2) ==> e2, if v is not free in e1 or e2." ]          .+ Eval .+ Shallow
--    , external "let-constructor-reuse" (promoteR $ not_defined "constructor-reuse" :: RewriteH Core)
--        [ "let v = C v1..vn in ... C v1..vn ... ==> let v = C v1..vn in ... v ..., fails otherwise" ] .+ Eval
    , external "let-float-app" (promoteExprR letFloatAppR :: RewriteH Core)
        [ "(let v = ev in e) x ==> let v = ev in e x" ]                         .+ Commute .+ Shallow
    , external "let-float-arg" (promoteExprR letFloatArgR :: RewriteH Core)
        [ "f (let v = ev in e) ==> let v = ev in f e" ]                         .+ Commute .+ Shallow
    , external "let-float-lam" (promoteExprR letFloatLamR :: RewriteH Core)
        [ "The Full Laziness Transformation"
        , "(\\ v1 -> let v2 = e1 in e2)  ==>  let v2 = e1 in (\\ v1 -> e2), if v1 is not free in e2."
        , "If v1 = v2 then v1 will be alpha-renamed." ]                         .+ Commute .+ Shallow
    , external "let-float-let" (promoteExprR letFloatLetR :: RewriteH Core)
        [ "let v = (let w = ew in ev) in e ==> let w = ew in let v = ev in e" ] .+ Commute .+ Shallow
    , external "let-float-case" (promoteExprR letFloatCaseR :: RewriteH Core)
        [ "case (let v = ev in e) of ... ==> let v = ev in case e of ..." ]     .+ Commute .+ Shallow .+ Eval
    , external "let-float-cast" (promoteExprR letFloatCastR :: RewriteH Core)
        [ "cast (let bnds in e) co ==> let bnds in cast e co" ]                 .+ Commute .+ Shallow
    , external "let-float-top" (promoteProgR letFloatTopR :: RewriteH Core)
        [ "v = (let bds in e) : prog ==> bds : v = e : prog" ]                  .+ Commute .+ Shallow
    , external "let-float" (promoteProgR letFloatTopR <+ promoteExprR letFloatExprR :: RewriteH Core)
        [ "Float a Let whatever the context." ]                                 .+ Commute .+ Shallow  -- Don't include in bash, as each sub-rewrite is tagged "Bash" already.
    , external "let-to-case" (promoteExprR letToCaseR :: RewriteH Core)
        [ "let v = ev in e ==> case ev of v -> e" ]                             .+ Commute .+ Shallow .+ PreCondition
--    , external "let-to-case-unbox" (promoteR $ not_defined "let-to-case-unbox" :: RewriteH Core)
--        [ "let v = ev in e ==> case ev of C v1..vn -> let v = C v1..vn in e" ]
    , external "let-unfloat" (promoteExprR letUnfloatR :: RewriteH Core)
        [ "Unfloat a let if possible." ]                                        .+ Commute .+ Shallow
    , external "let-unfloat-app" ((promoteExprR letUnfloatAppR >+> anybuR (promoteExprR letElimR)) :: RewriteH Core)
        [ "let v = ev in f a ==> (let v = ev in f) (let v = ev in a)" ]         .+ Commute .+ Shallow
    , external "let-unfloat-case" ((promoteExprR letUnfloatCaseR >+> anybuR (promoteExprR letElimR)) :: RewriteH Core)
        [ "let v = ev in case s of p -> e ==> case (let v = ev in s) of p -> let v = ev in e"
        , "if v does not shadow a pattern binder in p" ]                        .+ Commute .+ Shallow
    , external "let-unfloat-lam" ((promoteExprR letUnfloatLamR >+> anybuR (promoteExprR letElimR)) :: RewriteH Core)
        [ "let v = ev in \\ x -> e ==> \\ x -> let v = ev in e"
        , "if v does not shadow x" ]                                            .+ Commute .+ Shallow
    , external "reorder-lets" (promoteExprR . reorderNonRecLetsR :: [TH.Name] -> RewriteH Core)
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
                return body >>> substExprR v rhs

-- | This is quite expensive (O(n) for the size of the sub-tree).
--   Currently we always substitute types and coercions, and use a heuristic to decide whether to substitute expressions.
--   This may need revisiting.
safeLetSubstR :: forall c m. (AddBindings c, ExtendPath c Crumb, ReadBindings c, MonadCatch m) => Rewrite c m CoreExpr
safeLetSubstR =  prefixFailMsg "Safe let-substition failed: " $
                 withPatFailMsg ("expression is not a non-recursive let binding.") $
                 do e@(Let (NonRec v rhs) body) <- letAllR (tryR recToNonrecR) idR
                    when (isId v) (do safeSubstId <- letNonRecT mempty safeBindT (occursSafeToLetSubstId v) (\ () -> (||)) <<< return e
                                      guardMsg safeSubstId "safety criteria not met.")
                    return body >>> substExprR v rhs
                    -- TODO
                    -- guardMsg (not $ isCoVar v) "We consider it unsafe to substitute let-bound coercions.  I'm not sure why we think this."
  where
    -- what about other Expr constructors, e.g Cast?
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
letIntroR :: String -> Rewrite c HermitM CoreExpr
letIntroR nm = prefixFailMsg "Let-introduction failed: " $
              contextfreeT $ \ e -> do guardMsg (not $ isTypeArg e) "let expressions may not return a type."
                                       v <- newIdH nm (exprKindOrType e)
                                       return $ Let (NonRec v e) (Var v)

letElimR :: (ExtendPath c Crumb, AddBindings c, MonadCatch m) => Rewrite c m CoreExpr
letElimR = prefixFailMsg "Dead-let-elimination failed: " $
          withPatFailMsg (wrongExprForm "Let binds expr") $
          do Let bg _ <- idR
             case bg of
               NonRec{} -> letNonRecElimR
               Rec{}    -> letRecElimR

-- | Remove an unused non-recursive let binding.
--   @let v = E1 in E2@ ==> @E2@, if @v@ is not free in @E2@
letNonRecElimR :: MonadCatch m => Rewrite c m CoreExpr
letNonRecElimR = withPatFailMsg (wrongExprForm "Let (NonRec v e1) e2") $
                do Let (NonRec v _) e <- idR
                   guardMsg (v `notElemVarSet` exprFreeVars e) "let-bound variable appears in the expression."
                   return e

-- TODO: find the GHC way to do this, as this implementation will be defeated by mutual recursion
-- | Remove all unused recursive let bindings in the current group.
letRecElimR :: (ExtendPath c Crumb, AddBindings c, MonadCatch m) => Rewrite c m CoreExpr
letRecElimR = withPatFailMsg (wrongExprForm "Let (Rec v e1) e2") $
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
letToCaseR :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
letToCaseR = prefixFailMsg "Converting Let to Case failed: " $
            withPatFailMsg (wrongExprForm "Let (NonRec v e1) e2") $
  do Let (NonRec v ev) _ <- idR
     guardMsg (not $ isTyCoArg ev) "cannot case on a type or coercion."
     nameModifier <- freshNameGenT Nothing
     caseBndr <- constT (cloneVarH nameModifier v)
     letT mempty (replaceVarR v caseBndr) $ \ () e' -> Case ev caseBndr (varType v) [(DEFAULT, [], e')]

-------------------------------------------------------------------------------------------

-- | @(let v = ev in e) x@ ==> @let v = ev in e x@
letFloatAppR :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
letFloatAppR = prefixFailMsg "Let floating from App function failed: " $
  do vs <- appT (liftM mkVarSet letVarsT) exprFreeVarsT intersectVarSet
     let letAction = if isEmptyVarSet vs then idR else alphaLet
     appT letAction idR $ \ (Let bnds e) x -> Let bnds $ App e x

-- | @f (let v = ev in e)@ ==> @let v = ev in f e@
letFloatArgR :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
letFloatArgR = prefixFailMsg "Let floating from App argument failed: " $
  do vs <- appT exprFreeVarsT (liftM mkVarSet letVarsT) intersectVarSet
     let letAction = if isEmptyVarSet vs then idR else alphaLet
     appT idR letAction $ \ f (Let bnds e) -> Let bnds $ App f e

-- | @let v = (let w = ew in ev) in e@ ==> @let w = ew in let v = ev in e@
letFloatLetR :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
letFloatLetR = prefixFailMsg "Let floating from Let failed: " $
  do vs <- letNonRecT mempty (liftM mkVarSet letVarsT) exprFreeVarsT (\ () -> intersectVarSet)
     let bdsAction = if isEmptyVarSet vs then idR else nonRecAllR idR alphaLet
     letT bdsAction idR $ \ (NonRec v (Let bds ev)) e -> Let bds $ Let (NonRec v ev) e

-- | @(\ v -> let binds in e2)@  ==>  @let binds in (\ v1 -> e2)@
--   Fails if @v@ occurs in the RHS of @binds@.
--   If @v@ is shadowed in binds, then @v@ will be alpha-renamed.
letFloatLamR :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
letFloatLamR = prefixFailMsg "Let floating from Lam failed: " $
               withPatFailMsg (wrongExprForm "Lam v1 (Let (NonRec v2 e1) e2)") $
  do Lam v (Let binds body) <- idR
     (vs,fvs) <- lamT mempty (letT (arr bindVars &&& bindFreeVarsT) idR const) (\ () -> id)
     guardMsg (v `notElemVarSet` fvs) (var2String v ++ " occurs in the RHS of the let-bindings.")
     if v `elem` vs
      then alphaLam Nothing >>> letFloatLamR
      else return $ Let binds (Lam v body)

-- | @case (let bnds in e) of wild alts@ ==> @let bnds in (case e of wild alts)@
--   Fails if any variables bound in @bnds@ occurs in @alts@.
letFloatCaseR :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
letFloatCaseR = prefixFailMsg "Let floating from Case failed: " $
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
letFloatCastR :: MonadCatch m => Rewrite c m CoreExpr
letFloatCastR = prefixFailMsg "Let floating from Cast failed: " $
               withPatFailMsg (wrongExprForm "Cast (Let bnds e) co") $
  do Cast (Let bnds e) co <- idR
     return (Let bnds (Cast e co))

-- | Float a 'Let' through an expression, whatever the context.
letFloatExprR :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
letFloatExprR = setFailMsg "Unsuitable expression for Let floating." $
               letFloatArgR <+ letFloatAppR <+ letFloatLetR <+ letFloatLamR <+ letFloatCaseR <+ letFloatCastR

-- | @'ProgCons' ('NonRec' v ('Let' bds e)) p@ ==> @'ProgCons' bds ('ProgCons' ('NonRec' v e) p)@
letFloatTopR :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreProg
letFloatTopR = prefixFailMsg "Let floating to top level failed: " $
               withPatFailMsg (wrongExprForm "NonRec v (Let bds e) `ProgCons` p") $
               do vs <- consNonRecT mempty (liftM mkVarSet letIdsT) progFreeVarsT (\ () -> intersectVarSet)
                  let bdsAction = if isEmptyVarSet vs then idR else nonRecAllR idR alphaLet
                  progConsT bdsAction idR $ \ (NonRec v (Let bds ev)) p -> ProgCons bds (ProgCons (NonRec v ev) p)
  where
   letIdsT = letVarsT >>> acceptWithFailMsgR (all isId) "type and coercion bindings are not allowed at the top level."

-------------------------------------------------------------------------------------------

-- | Unfloat a 'Let' if possible.
letUnfloatR :: (ExtendPath c Crumb, AddBindings c, MonadCatch m) => Rewrite c m CoreExpr
letUnfloatR = letUnfloatCaseR <+ letUnfloatAppR <+ letUnfloatLamR

-- | @let v = ev in case s of p -> e@ ==> @case (let v = ev in s) of p -> let v = ev in e@,
--   if @v@ does not shadow a pattern binder in @p@
letUnfloatCaseR :: (ExtendPath c Crumb, AddBindings c, MonadCatch m) => Rewrite c m CoreExpr
letUnfloatCaseR = prefixFailMsg "Let unfloating from case failed: " $
                 withPatFailMsg (wrongExprForm "Let bnds (Case s w ty alts)") $
  do Let bnds (Case s w ty alts) <- idR
     captured <- letT (arr bindVars) caseVarsT intersect
     guardMsg (null captured) "let bindings would capture case pattern bindings."
     unbound <- letT (arr bindVars) (caseT mempty mempty tyVarsOfTypeT (const mempty) $ \ () () vs (_::[()]) -> varSetElems vs) intersect
     guardMsg (null unbound) "type variables in case signature would become unbound."
     return $ Case (Let bnds s) w ty $ mapAlts (Let bnds) alts

-- | @let v = ev in f a@ ==> @(let v = ev in f) (let v = ev in a)@
letUnfloatAppR :: MonadCatch m => Rewrite c m CoreExpr
letUnfloatAppR = prefixFailMsg "Let unfloating from app failed: " $
                withPatFailMsg (wrongExprForm "Let bnds (App e1 e2)") $
  do Let bnds (App e1 e2) <- idR
     return $ App (Let bnds e1) (Let bnds e2)

-- | @let v = ev in \ x -> e@ ==> @\x -> let v = ev in e@
--   if @v@ does not shadow @x@
letUnfloatLamR :: (ExtendPath c Crumb, AddBindings c, MonadCatch m) => Rewrite c m CoreExpr
letUnfloatLamR = prefixFailMsg "Let unfloating from lambda failed: " $
                withPatFailMsg (wrongExprForm "Let bnds (Lam v e)") $
  do Let bnds (Lam v e) <- idR
     safe <- letT (arr bindVars) lamVarT $ flip notElem
     guardMsg safe "let bindings would capture lambda binding."
     return $ Lam v $ Let bnds e

-------------------------------------------------------------------------------------------

-- | Re-order a sequence of nested non-recursive let bindings.
--   The argument list should contain the let-bound variables, in the desired order.
reorderNonRecLetsR :: MonadCatch m => [TH.Name] -> Rewrite c m CoreExpr
reorderNonRecLetsR nms = prefixFailMsg "Reorder lets failed: " $
                 do guardMsg (not $ null nms) "no names given."
                    guardMsg (nodups nms) "duplicate names given."
                    e <- idR
                    (ves,x) <- setFailMsg "insufficient non-recursive lets." $ takeNonRecLets (length nms) e
                    guardMsg (noneFreeIn ves) "some of the bound variables appear in the right-hand-sides."
                    e' <- mkNonRecLets `liftM` mapM (lookupName ves) nms `ap` return x
                    guardMsg (not $ exprSyntaxEq e e') "bindings already in specified order."
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
