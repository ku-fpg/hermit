{-# LANGUAGE ScopedTypeVariables, TypeFamilies, FlexibleContexts, TupleSections #-}
module Language.HERMIT.Primitive.Fold
    ( externals
    , foldR
    , stashFoldR
    ) where

import GhcPlugins hiding (empty)

import Control.Applicative
import Control.Monad

import qualified Data.Map as Map

import Language.HERMIT.Monad
import Language.HERMIT.Context
import Language.HERMIT.External
import Language.HERMIT.Kure
import Language.HERMIT.GHC

import Language.HERMIT.Primitive.GHC hiding (externals)
import Language.HERMIT.Primitive.Unfold hiding (externals)

import qualified Language.Haskell.TH as TH

import Prelude hiding (exp)

------------------------------------------------------------------------

externals :: [External]
externals =
         [ external "fold" (promoteExprR . foldR)
                ["fold a definition"
                ,""
                ,"double :: Int -> Int"
                ,"double x = x + x"
                ,""
                ,"5 + 5 + 6"
                ,"any-bu (fold 'double)"
                ,"double 5 + 6"
                ,""
                ,"Note: due to associativity, if you wanted to fold 5 + 6 + 6, "
                ,"you first need to apply an associativity rewrite."
                ] .+ Context .+ Deep
         , external "fold" (promoteExprR . stashFoldR)
                ["Fold a remembered definition."] .+ Context .+ Deep
         ]

------------------------------------------------------------------------

stashFoldR :: String -> RewriteH CoreExpr
stashFoldR label = prefixFailMsg "Fold failed: " $
                   contextfreeT $ \ e -> do
    Def i rhs <- lookupDef label
    maybe (fail "no match.")
          return
          (fold i rhs e)

foldR :: TH.Name -> RewriteH CoreExpr
foldR nm =  prefixFailMsg "Fold failed: " $
    translate $ \ c e -> do
        i <- case filter (\i -> nm `cmpTHName2Id` i) $ Map.keys (hermitBindings c) of
                [i] -> return i
                _ -> fail "cannot find name."
        either fail
               (\(rhs,_d) -> maybe (fail "no match.")
                                   return
                                   (fold i rhs e))
               (getUnfolding False False i c)

fold :: Id -> CoreExpr -> CoreExpr -> Maybe CoreExpr
fold i lam exp = do
    let (vs,body) = foldArgs lam
        -- return Nothing if not equal, so sequence will fail below
        checkEqual :: Maybe CoreExpr -> Maybe CoreExpr -> Maybe CoreExpr
        checkEqual m1 m2 = ifM (exprEqual <$> m1 <*> m2) m1 Nothing

    al <- foldMatch vs [] body exp

    let m = Map.fromListWith checkEqual [(k,Just v) | (k,v) <- al ]

    es <- sequence [ join (Map.lookup v m) | v <- vs ]
    return $ mkCoreApps (Var i) es

-- | Collect arguments to function we are folding, so we can unify with them.
foldArgs :: CoreExpr -> ([Var], CoreExpr)
foldArgs = go []
    where go vs (Lam v e) = go (v:vs) e
          go vs e         = (reverse vs, e)

-- Note: Id in the concrete instance is first
-- (not the Id found in the definition we are trying to fold).
addAlpha :: Id -> Id -> [(Id,Id)] -> [(Id,Id)]
addAlpha rId lId alphas | rId == lId = alphas
                        | otherwise  = (rId,lId) : alphas

-- Note: return list can have duplicate keys, caller is responsible
-- for checking that dupes refer to same expression
foldMatch :: [Var]          -- ^ vars that can unify with anything
          -> [(Id,Id)]      -- ^ alpha equivalences, wherever there is binding
                            --   note: we depend on behavior of lookup here, so new entries
                            --         should always be added to the front of the list so
                            --         we don't have to explicity remove them when shadowing occurs
          -> CoreExpr       -- ^ pattern we are matching on
          -> CoreExpr       -- ^ expression we are checking
          -> Maybe [(Var,CoreExpr)] -- ^ mapping of vars to expressions, or failure
foldMatch vs as (Var i) e | i `elem` vs = return [(i,e)]
                          | otherwise   = case e of
                                            Var i' | maybe False (==i) (lookup i' as) -> return [(i,e)]
                                                   | i == i' -> return []
                                            _                -> Nothing
foldMatch _  _ (Lit l) (Lit l') | l == l' = return []
foldMatch vs as (App e a) (App e' a') = do
    x <- foldMatch vs as e e'
    y <- foldMatch vs as a a'
    return (x ++ y)
foldMatch vs as (Lam v e) (Lam v' e') = foldMatch (filter (==v) vs) (addAlpha v' v as) e e'
foldMatch vs as (Let (NonRec v rhs) e) (Let (NonRec v' rhs') e') = do
    x <- foldMatch vs as rhs rhs'
    y <- foldMatch (filter (==v) vs) (addAlpha v' v as) e e'
    return (x ++ y)
-- TODO: this depends on bindings being in the same order
foldMatch vs as (Let (Rec bnds) e) (Let (Rec bnds') e') | length bnds == length bnds' = do
    let vs' = filter (`elem` map fst bnds) vs
        as' = [ (v',v) | ((v,_),(v',_)) <- zip bnds bnds' ] ++ as
        bmatch (_,rhs) (_,rhs') = foldMatch vs' as' rhs rhs'
    x <- zipWithM bmatch bnds bnds'
    y <- foldMatch vs' as' e e'
    return (concat x ++ y)
foldMatch vs as (Tick t e) (Tick t' e') | t == t' = foldMatch vs as e e'
foldMatch vs as (Case s b ty alts) (Case s' b' ty' alts')
  | (eqType ty ty') && (length alts == length alts') = do
    let as' = addAlpha b' b as
    x <- foldMatch vs as' s s'
    let vs' = filter (/=b) vs
        altMatch (ac, is, e) (ac', is', e') | ac == ac' =
            foldMatch (filter (`notElem` is) vs') (zip is' is ++ as') e e'
        altMatch _ _ = Nothing
    y <- zipWithM altMatch alts alts'
    return (x ++ concat y)
foldMatch vs as (Cast e c)   (Cast e' c')  | coreEqCoercion c c' = foldMatch vs as e e'
foldMatch _ _   (Type t)     (Type t')     | eqType t t' = return []
foldMatch _ _   (Coercion c) (Coercion c') | coreEqCoercion c c' = return []
foldMatch _ _ _ _ = Nothing
