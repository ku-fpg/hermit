module HERMIT.Dictionary.Fold
    ( -- * Fold/Unfold Transformation
      externals
    , foldR
    , foldVarR
    , stashFoldR
    , stashFoldAnyR
      -- * Unlifted fold interface
    , fold
    )

where

import Control.Arrow
import Control.Applicative
import Control.Monad

import qualified Data.Map as Map

import HERMIT.Core
import HERMIT.Context
import HERMIT.Monad
import HERMIT.Kure
import HERMIT.External
import HERMIT.GHC

import HERMIT.Dictionary.Common (varBindingDepthT,inScope,findIdT)
import HERMIT.Dictionary.Inline hiding (externals)

import Prelude hiding (exp)

------------------------------------------------------------------------

externals :: [External]
externals =
    [ external "fold" (promoteExprR . foldR :: String -> RewriteH Core)
        [ "fold a definition"
        , ""
        , "double :: Int -> Int"
        , "double x = x + x"
        , ""
        , "5 + 5 + 6"
        , "any-bu (fold 'double)"
        , "double 5 + 6"
        , ""
        , "Note: due to associativity, if you wanted to fold 5 + 6 + 6, "
        , "you first need to apply an associativity rewrite." ]  .+ Context .+ Deep
    , external "fold-remembered" (promoteExprR . stashFoldR :: Label -> RewriteH Core)
        [ "Fold a remembered definition." ]                      .+ Context .+ Deep
    , external "fold-any" (promoteExprR stashFoldAnyR :: RewriteH Core)
        [ "Attempt to fold any of the remembered definitions." ] .+ Context .+ Deep
    ]

------------------------------------------------------------------------

stashFoldR :: ReadBindings c => Label -> Rewrite c HermitM CoreExpr
stashFoldR label = prefixFailMsg "Fold failed: " $
    translate $ \ c e -> do
        Def i rhs <- lookupDef label
        guardMsg (inScope c i) $ var2String i ++ " is not in scope.\n(A common cause of this error is trying to fold a recursive call while being in the body of a non-recursive definition.  This can be resolved by calling \"nonrec-to-rec\" on the non-recursive binding group.)"
        maybe (fail "no match.")
              return
              (fold i rhs e)

stashFoldAnyR :: ReadBindings c => Rewrite c HermitM CoreExpr
stashFoldAnyR = setFailMsg "Fold failed: no definitions could be folded." $
                catchesM =<< map stashFoldR <$> (Map.keys <$> constT getStash)

foldR :: ReadBindings c => String -> Rewrite c HermitM CoreExpr
foldR nm = prefixFailMsg "Fold failed: " $ do
    v <- findIdT nm
    foldVarR v Nothing

foldVarR :: ReadBindings c => Var -> Maybe BindingDepth -> Rewrite c HermitM CoreExpr
foldVarR v md = do
    case md of
        Nothing    -> return ()
        Just depth -> do depth' <- varBindingDepthT v
                         guardMsg (depth == depth') "Specified binding depth does not match that of variable binding, this is probably a shadowing occurrence."
    e <- idR
    (rhs,_) <- getUnfoldingT AllBinders <<< return v
    maybe (fail "no match.") return (fold v rhs e)

------------------------------------------------------------------------

countBinders :: CoreExpr -> Int
countBinders e = length vs
    where (vs,_) = collectBinders e

collectNBinders :: Int -> CoreExpr -> Maybe ([Var], CoreExpr)
collectNBinders = go []
  where
    go bs 0 e         = return (reverse bs, e)
    go bs i (Lam b e) = go (b:bs) (i-1) e
    go _ _  _         = Nothing

-- return Nothing if not equal, so sequence will fail below
checkEqual :: Maybe CoreExpr -> Maybe CoreExpr -> Maybe CoreExpr
checkEqual m1 m2 = ifM (exprAlphaEq <$> m1 <*> m2) m1 Nothing

fold :: Id -> CoreExpr -> CoreExpr -> Maybe CoreExpr
fold i lam exp = do
    (vs,body) <- collectNBinders (countBinders lam - countBinders exp) lam
    al <- foldMatch vs [] body exp

    let m = Map.fromListWith checkEqual [(k,Just v) | (k,v) <- al ]

    es <- sequence [ join (Map.lookup v m) | v <- vs ]
    return $ mkCoreApps (varToCoreExpr i) es

-- Note: Var in the concrete instance is first
-- (not the Var found in the definition we are trying to fold).
addAlpha :: Var -> Var -> [(Var,Var)] -> [(Var,Var)]
addAlpha rId lId alphas | rId == lId = alphas
                        | otherwise  = (rId,lId) : alphas

matchWithTypes :: [Var] -> [(Var,Var)] -> Id -> CoreExpr -> Maybe [(Var,CoreExpr)]
matchWithTypes vs as i e = do
    tys <- foldMatchType vs as (idType i) (exprType e)
    return $ (i,e) : tyMatchesToCoreExpr tys

tyMatchesToCoreExpr :: [(TyVar, Type)] -> [(Var, CoreExpr)]
tyMatchesToCoreExpr = map (\(v,t) -> (v, Type t))

------------------------------------------------------------------------

-- Note: return list can have duplicate keys, caller is responsible
-- for checking that dupes refer to same expression
foldMatch :: [Var]          -- ^ vars that can unify with anything
          -> [(Var,Var)]    -- ^ alpha equivalences, wherever there is binding
                            --   note: we depend on behavior of lookup here, so new entries
                            --         should always be added to the front of the list so
                            --         we don't have to explicity remove them when shadowing occurs
          -> CoreExpr       -- ^ pattern we are matching on
          -> CoreExpr       -- ^ expression we are checking
          -> Maybe [(Var,CoreExpr)] -- ^ mapping of vars to expressions, or failure

foldMatch vs as (Var i) e | i `elem` vs = matchWithTypes vs as i e
                          | otherwise   = case e of
                                            Var i' | maybe False (==i) (lookup i' as) -> matchWithTypes vs as i e
                                                   | i == i' -> liftM tail $ matchWithTypes vs as i e 
                                                                -- note we depend on (i,e) being at front here
                                                                -- this is not strictly necessary, but is faster
                                            _                -> Nothing
foldMatch _  _ (Lit l) (Lit l') | l == l' = return []

foldMatch vs as (App e a) (App e' a') = do
    x <- foldMatch vs as e e'
    y <- foldMatch vs as a a'
    return (x ++ y)

foldMatch vs as (Lam v e) (Lam v' e') = foldMatch (filter (/=v) vs) (addAlpha v' v as) e e'

foldMatch vs as (Let (NonRec v rhs) e) (Let (NonRec v' rhs') e') = do
    x <- foldMatch vs as rhs rhs'
    y <- foldMatch (filter (/=v) vs) (addAlpha v' v as) e e'
    return (x ++ y)

-- TODO: this depends on bindings being in the same order
foldMatch vs as (Let (Rec bnds) e) (Let (Rec bnds') e') | length bnds == length bnds' = do
    let vs' = filter (`notElem` map fst bnds) vs
        as' = foldr (uncurry addAlpha) as $ zip (map fst bnds) (map fst bnds')
        bmatch (_,rhs) (_,rhs') = foldMatch vs' as' rhs rhs'
    x <- zipWithM bmatch bnds bnds'
    y <- foldMatch vs' as' e e'
    return (concat x ++ y)

foldMatch vs as (Tick t e) (Tick t' e') | t == t' = foldMatch vs as e e'

foldMatch vs as (Case s b ty alts) (Case s' b' ty' alts') = do
    guard (length alts == length alts')
    t <- foldMatchType vs as ty ty'
    x <- foldMatch vs as s s'
    let as' = addAlpha b' b as
        vs' = filter (/=b) vs
        altMatch (ac, is, e) (ac', is', e') | ac == ac' =
            foldMatch (filter (`notElem` is) vs') (foldr (uncurry addAlpha) as' $ zip is' is) e e'
        altMatch _ _ = Nothing
    y <- zipWithM altMatch alts alts'
    return (x ++ tyMatchesToCoreExpr t ++ concat y)

foldMatch vs as (Cast e c) (Cast e' c') = do
    guard (coreEqCoercion c c') 
    foldMatch vs as e e'

foldMatch vs as (Type t1) (Type t2) = liftM tyMatchesToCoreExpr $ foldMatchType vs as t1 t2

-- TODO: do we want to descend into these? There are Types in here.
foldMatch _ _ (Coercion c) (Coercion c') | coreEqCoercion c c' = return []

foldMatch _ _ _ _ = Nothing

------------------------------------------------------------------------

foldMatchType :: [TyVar]              -- ^ vars that can unify with anything
              -> [(TyVar,TyVar)]      -- ^ alpha equivalences, wherever there is binding
                                      --   note: we depend on behavior of lookup here, so new entries
                                      --         should always be added to the front of the list so
                                      --         we don't have to explicity remove them when shadowing occurs
              -> Type                 -- ^ pattern we are matching on
              -> Type                 -- ^ expression we are checking
              -> Maybe [(TyVar,Type)] -- ^ mapping of vars to types, or failure

foldMatchType vs as (TyVarTy v) t | v `elem` vs = return [(v,t)]
                                  | otherwise = case t of
                                                  TyVarTy v' | maybe False (==v) (lookup v' as) -> return [(v,t)]
                                                             | v == v' {- compare kinds? -} -> return []
                                                  _ -> Nothing

foldMatchType vs as (AppTy ty1 ty2) (AppTy ty1' ty2') = do
    x <- foldMatchType vs as ty1 ty1'
    y <- foldMatchType vs as ty2 ty2'
    return (x ++ y)

foldMatchType vs as (TyConApp tc1 kOrTys1) (TyConApp tc2 kOrTys2) = do
    guard ((tc1 == tc2) && (length kOrTys1 == length kOrTys2))
    let f ty1 ty2 | isKind ty1 && eqKind ty1 ty2 = return []
                  | otherwise = foldMatchType vs as ty1 ty2
    liftM concat $ zipWithM f kOrTys1 kOrTys2
    
foldMatchType vs as (FunTy ty1 ty2) (FunTy ty1' ty2') = do
    x <- foldMatchType vs as ty1 ty1'
    y <- foldMatchType vs as ty2 ty2'
    return (x ++ y)

foldMatchType vs as (ForAllTy v ty) (ForAllTy v' ty') = foldMatchType (filter (/=v) vs) (addAlpha v' v as) ty ty'

foldMatchType _ _ (LitTy l1) (LitTy l2) | l1 == l2 = return []

foldMatchType _ _ _ _ = Nothing

