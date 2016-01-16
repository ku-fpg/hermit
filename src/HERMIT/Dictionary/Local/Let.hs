{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE ScopedTypeVariables #-}

module HERMIT.Dictionary.Local.Let
    ( -- * Rewrites on Let Expressions
      externals
      -- ** Let Elimination
    , letNonRecSubstR
    , letNonRecSubstSafeR
    , letSubstR
    , letSubstSafeR
    , letElimR
    , letNonRecElimR
    , letRecElimR
    , progBindElimR
    , progBindNonRecElimR
    , progBindRecElimR
      -- ** Let Introduction
    , letIntroR
    , letNonRecIntroR
    , progNonRecIntroR
    , nonRecIntroR
    , letIntroUnfoldingR
      -- ** Let Floating Out
    , letFloatAppR
    , letFloatArgR
    , letFloatLetR
    , letFloatLamR
    , letFloatCaseR
    , letFloatCaseAltR
    , letFloatCastR
    , letFloatExprR
    , letFloatTopR
      -- ** Let Floating In
    , letFloatInR
    , letFloatInAppR
    , letFloatInCaseR
    , letFloatInLamR
      -- ** Miscallaneous
    , reorderNonRecLetsR
    , letTupleR
    , letToCaseR
    ) where

import Control.Arrow
import Control.Monad 
import Control.Monad.IO.Class

import Data.List (intersect, partition)
import Data.Monoid

import HERMIT.Core
import HERMIT.Context
import HERMIT.Monad
import HERMIT.Kure
import HERMIT.External
import HERMIT.GHC
import HERMIT.Name
import HERMIT.Utilities

import HERMIT.Dictionary.Common
import HERMIT.Dictionary.GHC hiding (externals)
import HERMIT.Dictionary.Inline hiding (externals)
import HERMIT.Dictionary.AlphaConversion hiding (externals)

import HERMIT.Dictionary.Local.Bind hiding (externals)

------------------------------------------------------------------------------

-- | Externals relating to 'Let' expressions.
externals :: [External]
externals =
    [ external "let-subst" (promoteExprR letSubstR :: RewriteH LCore)
        [ "Let substitution: (let x = e1 in e2) ==> (e2[e1/x])"
        , "x must not be free in e1." ]                                         .+ Deep .+ Eval
    , external "let-subst-safe" (promoteExprR letSubstSafeR :: RewriteH LCore)
        [ "Safe let substitution"
        , "let x = e1 in e2, safe to inline without duplicating work ==> e2[e1/x],"
        , "x must not be free in e1." ]                                         .+ Deep .+ Eval
    , external "let-nonrec-subst-safe" (promoteExprR letNonRecSubstSafeR :: RewriteH LCore)
        [ "As let-subst-safe, but does not try to convert a recursive let into a non-recursive let first." ] .+ Deep .+ Eval
    -- , external "safe-let-subst-plus" (promoteExprR safeLetSubstPlusR :: RewriteH LCore)
    --     [ "Safe let substitution"
    --     , "let { x = e1, ... } in e2, "
    --     , "  where safe to inline without duplicating work ==> e2[e1/x,...],"
    --     , "only matches non-recursive lets" ]  .+ Deep .+ Eval
    , external "let-intro" (promoteExprR . letIntroR :: String -> RewriteH LCore)
        [ "e => (let v = e in v), name of v is provided" ]                      .+ Shallow .+ Introduce
    , external "let-intro-unfolding" (promoteExprR . letIntroUnfoldingR :: HermitName -> RewriteH LCore)
        [ "e => let f' = defn[f'/f] in e[f'/f], name of f is provided" ]
    , external "let-elim" (promoteExprR letElimR :: RewriteH LCore)
        [ "Remove an unused let binding."
        , "(let v = e1 in e2) ==> e2, if v is not free in e1 or e2." ]          .+ Eval .+ Shallow
--    , external "let-constructor-reuse" (promoteR $ not_defined "constructor-reuse" :: RewriteH LCore)
--        [ "let v = C v1..vn in ... C v1..vn ... ==> let v = C v1..vn in ... v ..., fails otherwise" ] .+ Eval
    , external "let-float-app" (promoteExprR letFloatAppR :: RewriteH LCore)
        [ "(let v = ev in e) x ==> let v = ev in e x" ]                         .+ Commute .+ Shallow
    , external "let-float-arg" (promoteExprR letFloatArgR :: RewriteH LCore)
        [ "f (let v = ev in e) ==> let v = ev in f e" ]                         .+ Commute .+ Shallow
    , external "let-float-lam" (promoteExprR letFloatLamR :: RewriteH LCore)
        [ "The Full Laziness Transformation"
        , "(\\ v1 -> let v2 = e1 in e2)  ==>  let v2 = e1 in (\\ v1 -> e2), if v1 is not free in e2."
        , "If v1 = v2 then v1 will be alpha-renamed." ]                         .+ Commute .+ Shallow
    , external "let-float-let" (promoteExprR letFloatLetR :: RewriteH LCore)
        [ "let v = (let w = ew in ev) in e ==> let w = ew in let v = ev in e" ] .+ Commute .+ Shallow
    , external "let-float-case" (promoteExprR letFloatCaseR :: RewriteH LCore)
        [ "case (let v = ev in e) of ... ==> let v = ev in case e of ..." ]     .+ Commute .+ Shallow .+ Eval
    , external "let-float-case-alt" (promoteExprR (letFloatCaseAltR Nothing) :: RewriteH LCore)
        [ "case s of { ... ; p -> let v = ev in e ; ... } "
        , "==> let v = ev in case s of { ... ; p -> e ; ... } " ]               .+ Commute .+ Shallow .+ Eval
    , external "let-float-case-alt" (promoteExprR . letFloatCaseAltR . Just :: Int -> RewriteH LCore)
        [ "Float a let binding from specified alternative."
        , "case s of { ... ; p -> let v = ev in e ; ... } "
        , "==> let v = ev in case s of { ... ; p -> e ; ... } " ]               .+ Commute .+ Shallow .+ Eval
    , external "let-float-cast" (promoteExprR letFloatCastR :: RewriteH LCore)
        [ "cast (let bnds in e) co ==> let bnds in cast e co" ]                 .+ Commute .+ Shallow
    , external "let-float-top" (promoteProgR letFloatTopR :: RewriteH LCore)
        [ "v = (let bds in e) : prog ==> bds : v = e : prog" ]                  .+ Commute .+ Shallow
    , external "let-float" (promoteProgR letFloatTopR <+ promoteExprR letFloatExprR :: RewriteH LCore)
        [ "Float a Let whatever the context." ]                                 .+ Commute .+ Shallow  -- Don't include in bash, as each sub-rewrite is tagged "Bash" already.
    , external "let-to-case" (promoteExprR letToCaseR :: RewriteH LCore)
        [ "let v = ev in e ==> case ev of v -> e" ]                             .+ Commute .+ Shallow .+ PreCondition
--    , external "let-to-case-unbox" (promoteR $ not_defined "let-to-case-unbox" :: RewriteH LCore)
--        [ "let v = ev in e ==> case ev of C v1..vn -> let v = C v1..vn in e" ]
    , external "let-float-in" (promoteExprR letFloatInR >+> anybuR (promoteExprR letElimR) :: RewriteH LCore)
        [ "Float-in a let if possible." ]                                        .+ Commute .+ Shallow
    , external "let-float-in-app" ((promoteExprR letFloatInAppR >+> anybuR (promoteExprR letElimR)) :: RewriteH LCore)
        [ "let v = ev in f a ==> (let v = ev in f) (let v = ev in a)" ]         .+ Commute .+ Shallow
    , external "let-float-in-case" ((promoteExprR letFloatInCaseR >+> anybuR (promoteExprR letElimR)) :: RewriteH LCore)
        [ "let v = ev in case s of p -> e ==> case (let v = ev in s) of p -> let v = ev in e"
        , "if v does not shadow a pattern binder in p" ]                        .+ Commute .+ Shallow
    , external "let-float-in-lam" ((promoteExprR letFloatInLamR >+> anybuR (promoteExprR letElimR)) :: RewriteH LCore)
        [ "let v = ev in \\ x -> e ==> \\ x -> let v = ev in e"
        , "if v does not shadow x" ]                                            .+ Commute .+ Shallow
    , external "reorder-lets" (promoteExprR . reorderNonRecLetsR :: [String] -> RewriteH LCore)
        [ "Re-order a sequence of nested non-recursive let bindings."
        , "The argument list should contain the let-bound variables, in the desired order." ]
    , external "let-tuple" (promoteExprR . letTupleR :: String -> RewriteH LCore)
        [ "Combine nested non-recursive lets into case of a tuple."
        , "E.g. let {v1 = e1 ; v2 = e2 ; v3 = e3} in body ==> case (e1,e2,e3) of {(v1,v2,v3) -> body}" ] .+ Commute
    , external "prog-bind-elim" (promoteProgR progBindElimR :: RewriteH LCore)
        [ "Remove unused top-level binding(s)."
        , "prog-bind-nonrec-elim <+ prog-bind-rec-elim" ]                       .+ Eval .+ Shallow
    , external "prog-bind-nonrec-elim" (promoteProgR progBindNonRecElimR :: RewriteH LCore)
        [ "Remove unused top-level binding(s)."
        , "v = e : prog ==> prog, if v is not free in prog and not exported." ] .+ Eval .+ Shallow
    , external "prog-bind-rec-elim" (promoteProgR progBindRecElimR :: RewriteH LCore)
        [ "Remove unused top-level binding(s)."
        , "v+ = e+ : prog ==> v* = e* : prog, where v* is a subset of v+ consisting"
        , "of vs that are free in prog or e+, or exported." ]                   .+ Eval .+ Shallow
    ]

-------------------------------------------------------------------------------------------

-- | (let x = e1 in e2) ==> (e2[e1/x]), (x must not be free in e1)
letSubstR :: (AddBindings c, ExtendPath c Crumb, ReadPath c Crumb, MonadCatch m) => Rewrite c m CoreExpr
letSubstR = letAllR (tryR recToNonrecR) idR >>> letNonRecSubstR

-- | As 'letNonRecSubstSafeR', but attempting to convert a singleton recursive binding to a non-recursive binding first.
letSubstSafeR :: (AddBindings c, ExtendPath c Crumb, ReadPath c Crumb, ReadBindings c, HasEmptyContext c, MonadCatch m) => Rewrite c m CoreExpr
letSubstSafeR = letAllR (tryR recToNonrecR) idR >>> letNonRecSubstSafeR

-- | @Let (NonRec v e) body@ ==> @body[e/v]@
letNonRecSubstR :: MonadCatch m => Rewrite c m CoreExpr
letNonRecSubstR = prefixFailMsg "Let substitution failed: " $
                  withPatFailMsg (wrongExprForm "Let (NonRec v rhs) body") $
    do Let (NonRec v rhs) body <- idR
       return (substCoreExpr v rhs body)

{-
TODO: This was written very early in the project by Andy.
      It was later modified somewhat by Neil, but without reassessing the heurisitc as a whole.
      It may need revisiting.

Safe Subst Heuristic
--------------------

Substitution is safe if (A) OR (B) OR (C).

(A) The let-bound variable is a type or coercion.

(B) The let-bound value is either:
      (i)   a variable;
      (ii)  a lambda;
      (iii) an application that requires more value arguments before it can perform any computation.

(C) In the body, the let-bound variable must NOT occur:
      (i)  more than once;
      (ii) inside a lambda.

-}

-- | Currently we always substitute types and coercions, and use a heuristic to decide whether to substitute expressions.
--   This may need revisiting.
letNonRecSubstSafeR :: forall c m. (AddBindings c, ExtendPath c Crumb, ReadPath c Crumb, ReadBindings c, HasEmptyContext c, MonadCatch m) => Rewrite c m CoreExpr
letNonRecSubstSafeR =
    do Let (NonRec v _) _ <- idR
       when (isId v) $ guardMsgM (safeSubstT v) "safety criteria not met."
       letNonRecSubstR
  where
    safeSubstT :: Id -> Transform c m CoreExpr Bool
    safeSubstT i = letNonRecT mempty safeBindT (safeOccursT i) (\ () -> (||))

    -- what about other Expr constructors, e.g Cast?
    safeBindT :: Transform c m CoreExpr Bool
    safeBindT =
      do c <- contextT
         arr $ \ e ->
           case e of
             Var {} -> True
             Lam {} -> True
             App {} -> case collectArgs e of
                         (Var f,args) -> arityOf c f > length (filter (not . isTyCoArg) args) -- Neil: I've changed this to "not . isTyCoArg" rather than "not . isTypeArg".
                                                                                              -- This may not be the right thing to do though.
                         (other,args) -> case collectBinders other of
                                           (bds,_) -> length bds > length args
             _      -> False

    safeOccursT :: Id -> Transform c m CoreExpr Bool
    safeOccursT i =
      do depth <- varBindingDepthT i
         let occursHereT :: Transform c m Core ()
             occursHereT = promoteExprT (exprIsOccurrenceOfT i depth >>> guardT)

             -- lamOccurrenceT can only fail if the expression is not a Lam
             -- return either 2 (occurrence) or 0 (no occurrence)
             lamOccurrenceT :: Transform c m CoreExpr (Sum Int)
             lamOccurrenceT =  lamT mempty
                                    (mtryM (Sum 2 <$ extractT (onetdT occursHereT)))
                                    mappend

             occurrencesT :: Transform c m Core (Sum Int)
             occurrencesT = prunetdT (promoteExprT lamOccurrenceT <+ (Sum 1 <$ occursHereT))

         extractT occurrencesT >>^ (getSum >>> (< 2))

-------------------------------------------------------------------------------------------

letElimR :: MonadCatch m => Rewrite c m CoreExpr
letElimR = prefixFailMsg "Let elimination failed: " $
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
                   guardMsg (v `notElemVarSet` freeVarsExpr e) "let-bound variable appears in the expression."
                   return e

-- | Remove all unused recursive let bindings in the current group.
letRecElimR :: MonadCatch m => Rewrite c m CoreExpr
letRecElimR = withPatFailMsg (wrongExprForm "Let (Rec v e1) e2") $
    do Let (Rec bnds) body <- idR
       let bodyFrees   = freeIdsExpr body
           bsAndFrees  = map (second freeIdsExpr) bnds
           usedIds     = chaseDependencies bodyFrees bsAndFrees
           bs          = mkVarSet (map fst bsAndFrees)
           liveBinders = bs `intersectVarSet` usedIds
       if isEmptyVarSet liveBinders
          then return body
          else if bs `subVarSet` liveBinders
                 then fail "no dead binders to eliminate."
                 else return $ Let (Rec $ filter ((`elemVarSet` liveBinders) . fst) bnds) body

progBindElimR :: MonadCatch m => Rewrite c m CoreProg
progBindElimR = progBindNonRecElimR <+ progBindRecElimR

progBindNonRecElimR :: MonadCatch m => Rewrite c m CoreProg
progBindNonRecElimR = withPatFailMsg (wrongExprForm "ProgCons (NonRec v e1) e2") $ do
    ProgCons (NonRec v _) p <- idR
    guardMsg (v `notElemVarSet` freeVarsProg p) "variable appears in program body."
    guardMsg (not (isExportedId v)) "variable is exported."
    return p

-- | Remove all unused bindings at the top level.
progBindRecElimR :: MonadCatch m => Rewrite c m CoreProg
progBindRecElimR = withPatFailMsg (wrongExprForm "ProgCons (Rec v e1) e2") $
    do ProgCons (Rec bnds) p <- idR
       let pFrees      = freeVarsProg p
           bsAndFrees  = map (second freeIdsExpr) bnds
           usedIds     = chaseDependencies pFrees bsAndFrees
           bs          = mkVarSet (map fst bsAndFrees)
           liveBinders = (bs `intersectVarSet` usedIds) `unionVarSet` (filterVarSet isExportedId bs)
       if isEmptyVarSet liveBinders
          then return p
          else if bs `subVarSet` liveBinders
                 then fail "no dead binders to eliminate."
                 else return $ ProgCons (Rec $ filter ((`elemVarSet` liveBinders) . fst) bnds) p

chaseDependencies :: VarSet -> [(Var,VarSet)] -> VarSet
chaseDependencies usedIds bsAndFrees = case partition ((`elemVarSet` usedIds) . fst) bsAndFrees of
                                          ([],_)        -> usedIds
                                          (used,unused) -> chaseDependencies (unionVarSets (usedIds : map snd used)) unused

-------------------------------------------------------------------------------------------

-- | @let v = ev in e@ ==> @case ev of v -> e@
letToCaseR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, ReadBindings c, MonadCatch m, MonadUnique m)
           => Rewrite c m CoreExpr
letToCaseR = prefixFailMsg "Converting Let to Case failed: " $
            withPatFailMsg (wrongExprForm "Let (NonRec v e1) e2") $
  do Let (NonRec v ev) _ <- idR
     guardMsg (not $ isTyCoArg ev) "cannot case on a type or coercion."
     caseBndr <- extractT (cloneVarAvoidingT v Nothing [v])
     letT mempty (replaceVarR v caseBndr) $ \ () e' -> Case ev caseBndr (varType v) [(DEFAULT, [], e')]

-------------------------------------------------------------------------------------------

-- | @(let v = ev in e) x@ ==> @let v = ev in e x@
letFloatAppR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, BoundVars c, MonadCatch m, MonadUnique m)
             => Rewrite c m CoreExpr
letFloatAppR = prefixFailMsg "Let floating from App function failed: " $
               withPatFailMsg (wrongExprForm "App (Let bnds body) e") $
  do App (Let bnds body) e <- idR
     let vs = mkVarSet (bindVars bnds) `intersectVarSet` freeVarsExpr e
     if isEmptyVarSet vs
        then return $ Let bnds (App body e)
        else appAllR (alphaLetVarsR $ varSetElems vs) idR >>> letFloatAppR

-- | @f (let v = ev in e)@ ==> @let v = ev in f e@
letFloatArgR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, BoundVars c, MonadCatch m, MonadUnique m)
             => Rewrite c m CoreExpr
letFloatArgR = prefixFailMsg "Let floating from App argument failed: " $
               withPatFailMsg (wrongExprForm "App f (Let bnds body)") $
  do App f (Let bnds body) <- idR
     let vs = mkVarSet (bindVars bnds) `intersectVarSet` freeVarsExpr f
     if isEmptyVarSet vs
        then return $ Let bnds (App f body)
        else appAllR idR (alphaLetVarsR $ varSetElems vs) >>> letFloatArgR

-- | @let v = (let bds in e1) in e2@ ==> @let bds in let v = e1 in e2@
letFloatLetR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, BoundVars c, MonadCatch m, MonadUnique m)
             => Rewrite c m CoreExpr
letFloatLetR = prefixFailMsg "Let floating from Let failed: " $
               withPatFailMsg (wrongExprForm "Let (NonRec v (Let bds e1)) e2") $
  do Let (NonRec v (Let bds e1)) e2 <- idR
     let vs = mkVarSet (bindVars bds) `intersectVarSet` freeVarsExpr e2
     if isEmptyVarSet vs
       then return $ Let bds (Let (NonRec v e1) e2)
       else letNonRecAllR idR (alphaLetVarsR $ varSetElems vs) idR >>> letFloatLetR

-- | @(\ v -> let binds in e2)@  ==>  @let binds in (\ v1 -> e2)@
--   Fails if @v@ occurs in the RHS of @binds@.
--   If @v@ is shadowed in binds, then @v@ will be alpha-renamed.
letFloatLamR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, BoundVars c, MonadCatch m, MonadUnique m)
             => Rewrite c m CoreExpr
letFloatLamR = prefixFailMsg "Let floating from Lam failed: " $
               withPatFailMsg (wrongExprForm "Lam v1 (Let bds body)") $
  do Lam v (Let binds body) <- idR
     let bs  = bindVars binds
         fvs = freeVarsBind binds
     guardMsg (v `notElemVarSet` fvs) (unqualifiedName v ++ " occurs in the RHS of the let-bindings.")
     if v `elem` bs
      then alphaLamR Nothing >>> letFloatLamR
      else return $ Let binds (Lam v body)

-- | @case (let bnds in e) of bndr alts@ ==> @let bnds in (case e of bndr alts)@
--   Fails if any variables bound in @bnds@ occurs in @alts@.
letFloatCaseR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, BoundVars c, MonadCatch m, MonadUnique m)
              => Rewrite c m CoreExpr
letFloatCaseR = prefixFailMsg "Let floating from Case failed: " $
                withPatFailMsg (wrongExprForm "Case (Let bnds e) w ty alts") $
  do Case (Let bnds e) w ty alts <- idR
     let captures = mkVarSet (bindVars bnds) `intersectVarSet` delVarSet (unionVarSets $ map freeVarsAlt alts) w
     if isEmptyVarSet captures
       then return $ Let bnds (Case e w ty alts)
       else caseAllR (alphaLetVarsR $ varSetElems captures) idR idR (const idR) >>> letFloatCaseR

-- | case e of w { ... ; p -> let b = rhs in body ; ... }  ==>
--   let b = rhs in case e of { ... ; p -> body ; ... }
--
-- where no variable in `p` or `w` occurs freely in `rhs`,
-- and where `b` does not capture a free variable in the overall case,
-- and where `w` is not rebound in `b`.
letFloatCaseAltR :: MonadCatch m => Maybe Int -> Rewrite c m CoreExpr
letFloatCaseAltR maybeN = prefixFailMsg "Let float from case alternative failed: " $
                          withPatFailMsg (wrongExprForm "Case s w ty alts") $ do
        -- Perform the first safe let-floating out of a case alternative
    let letFloatOneAltM :: MonadCatch m => Id -> VarSet -> [CoreAlt] -> m (CoreBind,[CoreAlt])
        letFloatOneAltM w fvs = go
            where go [] = fail "no lets can be safely floated from alternatives."
                  go (alt:rest) = (do (bind,alt') <- letFloatAltM w fvs alt
                                      return (bind,alt':rest))
                                  <+ liftM (second (alt :)) (go rest)

        -- (p -> let bnds in body) ==> (bnds, p -> body)
        letFloatAltM :: Monad m => Id -> VarSet -> CoreAlt -> m (CoreBind,CoreAlt)
        letFloatAltM w fvs (con, vs, Let bnds body) = do
          let bSet = mkVarSet (bindVars bnds)
              vSet = mkVarSet (w:vs)

          -- 'w' is not in 'fvs', but if it is rebound by 'b', doing this rewrite
          -- would cause it to bind things that were previously bound by 'b'.
          guardMsg (not (w `elemVarSet` bSet)) "floating would allow case binder to capture variables."

          -- no free vars in 'rhs' are bound by 'p' or 'w'
          guardMsg (isEmptyVarSet $ vSet `intersectVarSet` freeVarsBind bnds)
                   "floating would cause variables in rhs to become unbound."

          -- no free vars in overall case are bound by 'b'
          guardMsg (isEmptyVarSet $ bSet `intersectVarSet` fvs)
                   "floating would cause let binders to capture variables in case expression."

          return (bnds, (con, vs, body))
        letFloatAltM _ _ _ = fail "no let expression on alternative right-hand side."

    Case e w ty alts <- idR
    fvs <- arr freeVarsExpr
    let l = length alts - 1
    case maybeN of
        Just n | n < 0 || n > l -> fail $ "valid alternative indices: 0 to " ++ show l
               | otherwise      -> do
            let (pre, alt:suf) = splitAt n alts
            (bnds,alt') <- letFloatAltM w fvs alt
            return $ Let bnds $ Case e w ty $ pre ++ (alt':suf)
        Nothing -> do
            (bnds,alts') <- letFloatOneAltM w fvs alts
            return $ Let bnds $ Case e w ty alts'

-- | @cast (let bnds in e) co@ ==> @let bnds in cast e co@
letFloatCastR :: MonadCatch m => Rewrite c m CoreExpr
letFloatCastR = prefixFailMsg "Let floating from Cast failed: " $
                withPatFailMsg (wrongExprForm "Cast (Let bnds e) co") $
  do Cast (Let bnds e) co <- idR
     return $ Let bnds (Cast e co)

-- | Float a 'Let' through an expression, whatever the context.
letFloatExprR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, BoundVars c, MonadCatch m, MonadUnique m)
              => Rewrite c m CoreExpr
letFloatExprR = setFailMsg "Unsuitable expression for Let floating."
              $ letFloatArgR <+ letFloatAppR <+ letFloatLetR <+ letFloatLamR
                  <+ letFloatCaseR <+ letFloatCaseAltR Nothing <+ letFloatCastR

-- | @'ProgCons' ('NonRec' v ('Let' bds e)) p@ ==> @'ProgCons' bds ('ProgCons' ('NonRec' v e) p)@
letFloatTopR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, BoundVars c, MonadCatch m, MonadUnique m)
             => Rewrite c m CoreProg
letFloatTopR = prefixFailMsg "Let floating to top level failed: " $
               withPatFailMsg (wrongExprForm "NonRec v (Let bds e) `ProgCons` p") $
               do ProgCons (NonRec v (Let bds e)) p <- idR
                  let bs = bindVars bds
                  guardMsg (all isId bs) "type and coercion bindings are not allowed at the top level."
                  let vs = intersectVarSet (mkVarSet bs) (freeVarsProg p)
                  if isEmptyVarSet vs
                    then return $ ProgCons bds (ProgCons (NonRec v e) p)
                    else consNonRecAllR idR (alphaLetVarsR $ varSetElems vs) idR >>> letFloatTopR

-------------------------------------------------------------------------------------------

-- | Float in a 'Let' if possible.
letFloatInR :: (AddBindings c, BoundVars c, ExtendPath c Crumb, ReadPath c Crumb, MonadCatch m, MonadUnique m)
            => Rewrite c m CoreExpr
letFloatInR = letFloatInCaseR <+ letFloatInAppR <+ letFloatInLamR

-- | @let v = ev in case s of p -> e@ ==> @case (let v = ev in s) of p -> let v = ev in e@,
--   if @v@ does not shadow a pattern binder in @p@
letFloatInCaseR :: (AddBindings c, BoundVars c, ExtendPath c Crumb, ReadPath c Crumb, MonadCatch m, MonadUnique m)
                => Rewrite c m CoreExpr
letFloatInCaseR = prefixFailMsg "Let floating in to case failed: " $
                  withPatFailMsg (wrongExprForm "Let bnds (Case s w ty alts)") $
  do Let bnds (Case s w ty alts) <- idR
     let bs = bindVars bnds
         captured = bs `intersect` (w : concatMap altVars alts)
     guardMsg (null captured) "let bindings would capture case pattern bindings."
#if __GLASGOW_HASKELL__ > 710
     let unbound = mkVarSet bs `intersectVarSet` (tyCoVarsOfType ty `unionVarSet` freeVarsVar w)
#else
     let unbound = mkVarSet bs `intersectVarSet` (tyVarsOfType ty `unionVarSet` freeVarsVar w)
#endif
     guardMsg (isEmptyVarSet unbound) "type variables in case signature would become unbound."
     return (Case (Let bnds s) w ty alts) >>> caseAllR idR idR idR (\_ -> altAllR idR (\_ -> idR) (arr (Let bnds) >>> alphaLetR))

-- | @let v = ev in f a@ ==> @(let v = ev in f) (let v = ev in a)@
letFloatInAppR :: (AddBindings c, BoundVars c, ExtendPath c Crumb, ReadPath c Crumb, MonadCatch m, MonadUnique m)
               => Rewrite c m CoreExpr
letFloatInAppR = prefixFailMsg "Let floating in to app failed: " $
                withPatFailMsg (wrongExprForm "Let bnds (App e1 e2)") $
  do Let bnds (App e1 e2) <- idR
     lhs <- return (Let bnds e1) >>> alphaLetR
     return $ App lhs (Let bnds e2)

-- | @let v = ev in \ x -> e@ ==> @\x -> let v = ev in e@
--   if @v@ does not shadow @x@
letFloatInLamR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, MonadCatch m) => Rewrite c m CoreExpr
letFloatInLamR = prefixFailMsg "Let floating in to lambda failed: " $
                withPatFailMsg (wrongExprForm "Let bnds (Lam v e)") $
  do Let bnds (Lam v e) <- idR
     safe <- letT (arr bindVars) lamVarT $ flip notElem
     guardMsg safe "let bindings would capture lambda binding."
     return $ Lam v $ Let bnds e

-------------------------------------------------------------------------------------------

-- | Re-order a sequence of nested non-recursive let bindings.
--   The argument list should contain the let-bound variables, in the desired order.
reorderNonRecLetsR :: MonadCatch m => [String] -> Rewrite c m CoreExpr
reorderNonRecLetsR nms = prefixFailMsg "Reorder lets failed: " $
                 do guardMsg (notNull nms) "no names given."
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
                      in all (`notElemVarSet` unionVarSets (map freeVarsExpr es)) vs

    lookupName :: Monad m => [(Var,CoreExpr)] -> String -> m (Var,CoreExpr)
    lookupName ves nm = case filter (cmpString2Var nm . fst) ves of
                            []   -> fail $ "name " ++ nm ++ " not matched."
                            [ve] -> return ve
                            _    -> fail $ "multiple matches for " ++ nm ++ "."

    mkNonRecLets :: [(Var,CoreExpr)] -> CoreExpr -> CoreExpr
    mkNonRecLets []          x  = x
    mkNonRecLets ((v,e):ves) x  = Let (NonRec v e) (mkNonRecLets ves x)

-------------------------------------------------------------------------------------------

-- | Combine nested non-recursive lets into case of a tuple.
--   E.g. let {v1 = e1 ; v2 = e2 ; v3 = e3} in body ==> case (e1,e2,e3) of {(v1,v2,v3) -> body}
letTupleR :: (MonadCatch m, MonadUnique m) => String -> Rewrite c m CoreExpr
letTupleR nm = prefixFailMsg "Let-tuple failed: " $
      do (bnds, body) <- arr collectLets
         let numBnds = length bnds
         guardMsg (numBnds > 1) "at least two non-recursive let bindings of identifiers required."

         let (vs, rhss) = unzip bnds

         -- check if tupling the bindings would cause unbound variables
         let frees  = map freeVarsExpr (drop 1 rhss)
             used   = unionVarSets $ zipWith intersectVarSet (map (mkVarSet . (`take` vs)) [1..]) frees
         if isEmptyVarSet used
           then let rhs = mkCoreTup rhss
                in constT $ do bndr <- newIdH nm (exprType rhs)
                               return $ mkSmallTupleCase vs body bndr rhs

           else fail $ "the following bound variables are used in subsequent bindings: " ++ showVarSet used

  where
    -- we only collect identifiers (not type or coercion vars) because we intend to case on them.
    collectLets :: CoreExpr -> ([(Id, CoreExpr)],CoreExpr)
    collectLets (Let (NonRec v e) body) | isId v = first ((v,e):) (collectLets body)
    collectLets expr                             = ([],expr)

-------------------------------------------------------------------------------------------

-- TODO: come up with a better naming scheme for these

-- This code could be factored better.

-- | @e@ ==> @let v = e in v@
letIntroR :: (MonadCatch m, MonadUnique m) => String -> Rewrite c m CoreExpr
letIntroR nm = do e <- idR
                  Let (NonRec v e') _ <- letNonRecIntroR nm e
                  return $ Let (NonRec v e') (varToCoreExpr v)

-- | @body@ ==> @let v = e in body@
letNonRecIntroR :: (MonadCatch m, MonadUnique m) => String -> CoreExpr -> Rewrite c m CoreExpr
letNonRecIntroR nm e = prefixFailMsg "Let-introduction failed: " $
     contextfreeT $ \ body -> do v <- case e of
                                        Type _ -> newTyVarH nm $ exprKindOrType e
                                        _      -> newIdH nm $ exprKindOrType e
                                 return $ Let (NonRec v e) body


-- This isn't a "Let", but it's serving the same role.  Maybe create a Local/Prog module?

-- | @prog@ ==> @'ProgCons' (v = e) prog@
progNonRecIntroR :: (MonadCatch m, MonadUnique m) => String -> CoreExpr -> Rewrite c m CoreProg
progNonRecIntroR nm e = prefixFailMsg "Top-level binding introduction failed: " $
  do guardMsg (not $ isTyCoArg e) "Top-level type or coercion definitions are prohibited."
     contextfreeT $ \ prog -> do i <- newIdH nm (exprType e)
                                 return $ ProgCons (NonRec i e) prog

-- | nonRecIntroR nm e = 'letNonRecIntroR nm e' <+ 'progNonRecIntroR nm e'
nonRecIntroR :: (MonadCatch m, MonadUnique m) => String -> CoreExpr -> Rewrite c m Core
nonRecIntroR nm e = readerT $ \case
                      ExprCore{} -> promoteExprR (letNonRecIntroR nm e)
                      ProgCore{} -> promoteProgR (progNonRecIntroR nm e)
                      _          -> fail "can only introduce non-recursive bindings at Program or Expression nodes."

-- | Introduce a local definition for a (possibly imported) identifier.
-- Rewrites occurences of the identifier to point to this new local definiton.
letIntroUnfoldingR :: ( ReadBindings c, HasHermitMEnv m, LiftCoreM m
                      , MonadCatch m, MonadIO m, MonadThings m, MonadUnique m )
                   => HermitName -> Rewrite c m CoreExpr
letIntroUnfoldingR nm = do
    i <- findIdT nm
    (rhs,_) <- getUnfoldingT AllBinders <<< return i
    contextfreeT $ \ body -> do
        i' <- cloneVarH id i
        let subst = substCoreExpr i (varToCoreExpr i')
            bnd = if i `elemUFM` freeVarsExpr rhs then Rec [(i', subst rhs)]
                                                  else NonRec i' rhs
            body' = subst body
        return $ mkCoreLet bnd body'
-------------------------------------------------------------------------------------------
