{-# LANGUAGE TypeFamilies, FlexibleContexts #-}
-- TODO: remove this module
module Language.HERMIT.Primitive.Subst where

import GhcPlugins hiding (empty)
import Data.List (intersect)

import Control.Arrow

import Language.HERMIT.Monad
import Language.HERMIT.Kure
import Language.HERMIT.External
import Language.HERMIT.Primitive.GHC(coreExprFreeIds)

import Language.HERMIT.Primitive.Common

import qualified Language.Haskell.TH as TH

import Prelude hiding (exp)
import Data.Maybe

externals :: [External]
externals =
         [  external "alpha" alpha
               [ "renames the bound variables at the current node."]
         ,  external "alpha-lam" (promoteExprR . alphaLam . Just)
               [ "renames the bound variable in a Lambda expression to the given name."]
         ,  external "alpha-lam" (promoteExprR $ alphaLam Nothing)
               [ "renames the bound variable in a Lambda expression."]
         ,  external "alpha-case-binder" (promoteExprR . alphaCaseBinder . Just)
               [ "renames the binder in a Case expression to the given name."]
         ,  external "alpha-case-binder" (promoteExprR $ alphaCaseBinder Nothing)
               [ "renames the binder in a Case expression."]
         ,  external "alpha-alt" (promoteAltR alphaAlt)
               [ "renames all binders in a Case alternative."]
         ,  external "alpha-case" (promoteExprR alphaCase)
               [ "renames all binders in a Case alternative."]
         ,  external "alpha-let" (promoteExprR . alphaLetOne . Just)
               [ "renames the bound variable in a Let expression with one binder to the given name."]
         ,  external "alpha-let" (promoteExprR $ alphaLet)
               [ "renames the bound variables in a Let expression."]
         ,  external "alpha-top" (promoteProgramR . alphaConsOne . Just)
               [ "renames the bound variable in a top-level binding with one binder to the given name."]
         ,  external "alpha-top" (promoteProgramR $ alphaCons)
               [ "renames the bound variables in a top-level binding."]
         ]

-- externals :: [External]
-- externals =
--          [
--            external "alpha" (\nm -> promoteExprR (alphaLambda (Just nm)) :: RewriteH Core)
--                 [ "alpha 'v renames the bound variable in a Lambda expression to v."]
--          , external "alpha" (promoteExprR (alphaLambda Nothing) :: RewriteH Core)
--                 [ "renames the bound variable in a lambda expression."]
--          , external "alpha-let" (promoteExprR alphaLet :: RewriteH Core)
--                 [ "Alpha rename for any Let expr."]
--          , external "alpha-let-nonrec" (\nm -> promoteExprR (alphaNonRecLet (Just nm)) :: RewriteH Core)
--                 [ "alpha-let-nonrec 'v renames the bound variable in a NonRecursive Let expression to v."]
--          , external "alpha-let-rec1" (\nm -> promoteExprR (alphaRecLetOne (Just nm)) :: RewriteH Core)
--                 [ "alpha-let-rec1 'v renames the bound variable in a Recursive Let expression (with a single binding) to v."]

--            -- the remaining are really just for testing.
--          , external "alpha-case" (promoteExprR alphaCase :: RewriteH Core)
--                 [ "renames the bound variables in a case expression."]
--          , external "alpha-alt" (promoteAltR alphaAlt :: RewriteH Core)
--                 [ "Alpha rename (for a single Case Alternative)."]
--          , external "alpha-case-wild" (\ nm -> promoteExprR (alphaCaseWild (Just nm)) :: RewriteH Core)
--                 [ "Alpha renaming for the wildcard pattern in a Case."]
--          , external "alpha-case-wild" (promoteExprR (alphaCaseWild Nothing) :: RewriteH Core)
--                 [ "Alpha renaming for the wildcard pattern in a Case."]
--          ]

-- bindList :: CoreBind -> [Id]
-- bindList (NonRec b _) = [b]
-- bindList (Rec binds)  = map fst binds

-- newVarName :: Id -> TH.Name
-- newVarName x = TH.mkName $ showSDoc (ppr x) ++ "New"

-- freshVarT :: Id -> TranslateH a Id
-- freshVarT v = constT $ newVarH (newVarName v) (idType v)

-- freshVarT' :: TH.Name -> Type -> TranslateH a Id
-- freshVarT' nm ty  = constT $ newVarH nm ty


-- -- The alpha renaming functions defined here,
-- -- rely on a function to return a globally fresh Id,
-- -- therefore, they do not require a list of Id's which must not clash.

-- alphaLambda :: Maybe TH.Name -> RewriteH CoreExpr
-- alphaLambda nm = do Lam b _ <- idR
--                     let newname = fromMaybe (newVarName b) nm
--                     b' <- freshVarT' newname (idType b)
--                     lamT (trySubstR b $ Var b') (\ _ -> Lam b')

-- -- Replace each var bound in a let expr with a globally fresh Id.
-- alphaLet :: RewriteH CoreExpr
-- alphaLet = alphaNonRecLet Nothing <+ alphaRecLet

-- alphaNonRecLet :: Maybe TH.Name -> RewriteH CoreExpr
-- alphaNonRecLet nm = do Let (NonRec v _) _ <- idR
--                        let newname = fromMaybe (newVarName v) nm
--                        v' <- freshVarT' newname (idType v)
--                        letNonRecT idR (trySubstR v $ Var v') (\ _ e1 e2 -> Let (NonRec v' e1) e2)

-- alphaRecLet :: RewriteH CoreExpr
-- alphaRecLet = do Let bds@(Rec _) _ <- idR
--                  let boundIds = bindList bds
--                  freshBoundIds <- sequence $ fmap freshVarT boundIds
--                  letRecDefT (\ _ -> foldr seqSubst idR (zip boundIds freshBoundIds))
--                             (foldr seqSubst idR (zip boundIds freshBoundIds))
--                             (\ bds' e' -> let freshBds = zip freshBoundIds (map snd bds') in Let (Rec freshBds) e')
--     where seqSubst (v,v') t = t >>> trySubstR v (Var v')


-- alphaRecLetOne :: Maybe TH.Name -> RewriteH CoreExpr
-- alphaRecLetOne nm = do Let (Rec [(v, _)]) _ <- idR
--                        let newname = fromMaybe (newVarName v) nm
--                        v' <- freshVarT' newname (idType v)
--                        letRecDefT (\ _ -> trySubstR v $ Var v')
--                                   (trySubstR v $ Var v')
--                                   (\ [(_,be)] e' -> Let (Rec [(v', be)]) e')

-- alphaCase :: RewriteH CoreExpr
-- alphaCase = alphaCaseWild Nothing >+> anyR (promoteAltR alphaAlt)

-- -- Only renames the wildcard identifier
-- alphaCaseWild :: Maybe TH.Name -> RewriteH CoreExpr
-- alphaCaseWild nm = do Case _ v _ _ <- idR
--                       let newname = fromMaybe (newVarName v) nm
--                       v' <- freshVarT' newname (idType v)
--                       caseT idR (\ _ -> tryR $ substAltR v $ Var v') (\ e _ -> Case e v')

-- alphaAlt :: RewriteH CoreAlt
-- alphaAlt = do (con, vs, _) <- idR
--               freshBoundIds <- sequence $ fmap freshVarT vs
--               altT (foldr seqSubst idR (zip vs freshBoundIds)) (\ _ _ e' -> (con, freshBoundIds, e'))
--     where seqSubst (v,v') t = t >>> trySubstR v (Var v')

-- -- Andy's substitution rewrite
-- --  E [ v::r ] ===   let (NonRec v = r) in E
-- --      and then inline "v"


-- -- | Substitution

-- -- for when we want to consider no change to be a success
-- trySubstR :: Id -> CoreExpr -> RewriteH CoreExpr
-- trySubstR v e = tryR (substR v e)

-- substR :: Id -> CoreExpr -> RewriteH CoreExpr
-- substR v expReplacement = (rule12 <+ rule345 <+ rule78 <+ rule9)  <+ rule6
--     where -- The 6 rules from the textbook for the simple lambda calculus.
--         rule12 :: RewriteH CoreExpr
--         rule12 = whenM (varT (==v)) (return expReplacement)

--         rule345 :: RewriteH CoreExpr
--         rule345 = do Lam b e <- idR
--                      guardMsg (b /= v) "Subtitution var clashes with Lam"
--                      guardMsg (v `elem` coreExprFreeIds e) "Substitution var not used in body of Lam"
--                      if b `elem` coreExprFreeIds expReplacement
--                       then alphaLambda Nothing >>> rule345
--                       else lamR (substR v expReplacement)

--         rule6 :: RewriteH CoreExpr
--         rule6 =  anyR (promoteExprR $ substR v expReplacement)

--         -- like Rule 3 and 4/5 above, but for lets
--         rule78 :: RewriteH CoreExpr
--         rule78 = do Let bds _e <- idR
--                     guardMsg (v `notElem` bindList bds) "Substitution variable clashes with Let var."
--                     if null $ List.intersect (bindList bds) (coreExprFreeIds expReplacement)
--                      then letAnyR (substBindR v expReplacement) (substR v expReplacement)
--                      else alphaLet >>> rule78

--         rule9 :: RewriteH CoreExpr
--         rule9 = do Case _ x _ _ <- idR
--                    guardMsg (x /= v) "Substitution variable clashes with Case wildcard."
--                    (if x `elem` coreExprFreeIds expReplacement
--                       then alphaCaseWild Nothing
--                       else idR) >>> caseAnyR (substR v expReplacement) (\_ -> substAltR v expReplacement)

-- -- edk !! Note, this subst handles name clashes with variables bound in the Alt form,
-- -- since the scope of these bound variables is within the Alt.
-- substAltR :: Id -> CoreExpr -> RewriteH CoreAlt
-- substAltR v expReplacement =
--     do (_, bs, _) <- idR
--        guardMsg (v `notElem` bs) "Substitution variable clashes with Alt binders"
--        (if null $ List.intersect bs (coreExprFreeIds expReplacement)
--          then idR
--          else alphaAlt) >>> altR (substR v expReplacement)


-- -- edk !! Note, this subst DOES NOT handle name clashes with variables bound in the Bind form,
-- -- since the scope of these bound variables extends beyond the form.
-- -- IF there is a name clash, the Bind is returned un-altered, rather than failure.
-- substBindR :: Id -> CoreExpr -> RewriteH CoreBind
-- substBindR v expReplacement = substNonRecBindR v expReplacement <+ substRecBindR v expReplacement

-- substNonRecBindR :: Id -> CoreExpr  -> RewriteH CoreBind
-- substNonRecBindR v expReplacement =
--     do NonRec b _ <- idR
--        guardMsg (b /= v) "Substitution var clashes wth Let bound var"
--        guardMsg (b `elem` coreExprFreeIds expReplacement) "Let bound var is free in substitution expr." -- TODO: alpha rename and continue?
--        nonRecR (substR v expReplacement)

-- substRecBindR :: Id -> CoreExpr  -> RewriteH CoreBind
-- substRecBindR v expReplacement =
--     do exp@(Rec _) <- idR
--        let boundIds = bindList exp
--        guardMsg (v `notElem` boundIds) "Substitution var clashes wth Let bound var"
--        guardMsg (not . null $ List.intersect boundIds (coreExprFreeIds expReplacement)) "Let bound var is free in substitution expr." -- TODO: alpha rename and continue?
--        recDefAnyR (\ _ -> substR v expReplacement)

-- -- TO DO: Rewrite this
-- letSubstR :: RewriteH CoreExpr
-- letSubstR = rewrite $ \ c exp ->
--     case exp of
--       Let (NonRec b be) e | isId b -> apply (substR b be) c e
--          -- For type subst, we use the GHC subst mechansim
--       Let (NonRec b (Type bty)) e | isTyVar b -> do
--                 let sub = extendTvSubst emptySubst b bty
--                 return $ substExpr (text "letSubstR") sub e
-- --         | otherwise -> fail "LetSubst failed. (is a type variable)"
--       _ -> fail "LetSubst failed. Expr is not a Non-recursive Let."

-- -- -- tests ...
-- -- alphaCase :: RewriteH CoreExpr
-- -- alphaCase = caseAnyR (fail "alphaCase") (\ _ -> alphaAlt)

-----------------------------------------------------------------------

-- trySubstR :: Id -> CoreExpr -> RewriteH Core
-- trySubstR v e = tryR (substR v e)

substR :: Id -> CoreExpr -> RewriteH Core
substR v e = promoteExprR (substVarR v e) <+ substNonVarR v e

substVarR :: Id -> CoreExpr -> RewriteH CoreExpr
substVarR v e = whenM (varT (==v)) (return e)

-- This defintition contains themain logic of the substitution algorithm
substNonVarR :: Id -> CoreExpr -> RewriteH Core
substNonVarR v e = let fvs = coreExprFreeIds e in
                   do bs <- arr idsBoundCore
                      if v `elem` bs
                        then substWhereBinderOutOfScopeR v e
                        else let xs = fvs `intersect` bs
                              in andR (map alphaRenameId xs) >>> anyR (substR v e)
                                 -- rename any binders that would capture free variables in the expression to
                                 -- be substituted in, then descend and continue substituting
  where
    alphaRenameId :: Id -> RewriteH Core
    alphaRenameId i =  promoteR (alphaConsNonRec Nothing <+ alphaConsRecId Nothing i)
                    <+ promoteR (alphaAltId Nothing i)
                    <+ promoteR (alphaLam Nothing <+ (alphaLetNonRec Nothing <+ alphaLetRecId Nothing i) <+ alphaCaseBinder Nothing)


-- | All the idenitifiers bound /at this level/.
idsBoundCore :: Core -> [Id]
idsBoundCore (ModGutsCore _)      = []
idsBoundCore (BindCore _)         = [] -- too low level, should have been dealt with higher up
idsBoundCore (DefCore _)          = [] -- too low level, should have been dealt with higher up
idsBoundCore (AltCore (_,vs,_))   = vs
idsBoundCore (ProgramCore p)      = case p of
                                      []    -> []
                                      (b:_) -> idsBoundBind b
idsBoundCore (ExprCore e)         = case e of
                                      Lam v _      -> [v]
                                      Let b _      -> idsBoundBind b
                                      Case _ v _ _ -> [v]  -- alternatives are dealt with lower down
                                      _            -> []

-- | All the identifiers bound in this binding group.
idsBoundBind :: CoreBind -> [Id]
idsBoundBind (NonRec b _) = [b]
idsBoundBind (Rec bs)     = map fst bs

-- | For situations where we have a node containing a binder /and/ a child that is not in scope of that binder,
--   this substitutes into that out-of-scope child.
substWhereBinderOutOfScopeR :: Id -> CoreExpr -> RewriteH Core
substWhereBinderOutOfScopeR v e =  promoteR (consBindAllR substNonRecR idR)
                                <+ promoteR (letAllR substNonRecR idR <+ caseAllR (substVarR v e) (const idR))
  where
    substNonRecR :: RewriteH CoreBind
    substNonRecR = nonRecR (substVarR v e)

-----------------------------------------------------------------------

newIdName :: Id -> TH.Name
newIdName x = TH.mkName $ showSDoc (ppr x) ++ "'"

-- | Takes a proposed new name, and the identifier that is being renamed.
freshId :: Maybe TH.Name -> Id -> HermitM Id
freshId mn v = let n = fromMaybe (newIdName v) mn
                in newVarH n (idType v)

-- | Lifted version of 'freshId'.
freshIdT :: Maybe TH.Name -> Id -> TranslateH a Id
freshIdT mn v = constT (freshId mn v)

-- | Arguments are the original identifier and the replacement identifier, respectively.
renameIdR :: (Injection a Core, Generic a ~ Core) => Id -> Id -> RewriteH a
renameIdR v v' = extractR $ tryR $ substR v (Var v')

-- | Given an identifier to replace, and a replacement, produce an 'Id' @->@ 'Id' function that
--   acts as in identity for all 'Id's except the one to replace, for which it returns the replacment.
--   Don't export this, it'll likely just cause confusion.
replaceId :: Id -> Id -> (Id -> Id)
replaceId v v' i = if v == i then v' else i

-----------------------------------------------------------------------

-- | Alpha rename a lambda binder.  Optionally takes a suggested new name.
alphaLam :: Maybe TH.Name -> RewriteH CoreExpr
alphaLam mn = setFailMsg ("alpha-lam failed: " ++ wrongExprForm "Lam v e") $
              do Lam v _ <- idR
                 v' <- freshIdT mn v
                 lamT (renameIdR v v') (\ _ -> Lam v')

-----------------------------------------------------------------------

-- | Alpha rename a case binder.  Optionally takes a suggested new name.
alphaCaseBinder :: Maybe TH.Name -> RewriteH CoreExpr
alphaCaseBinder mn = do Case _ v _ _ <- idR
                        v' <- freshIdT mn v
                        caseT idR (\ _ -> renameIdR v v') (\ e _ t alts -> Case e v' t alts)

-----------------------------------------------------------------------

-- | Rename the specified identifier in a case alternative.  Optionally takes a suggested new name.
alphaAltId :: Maybe TH.Name -> Id -> RewriteH CoreAlt
alphaAltId mn v = do v' <- freshIdT mn v
                     altT (renameIdR v v') (\ con vs e -> (con, map (replaceId v v') vs, e))

-- | Rename all identifiers bound in a case alternative.
alphaAlt :: RewriteH CoreAlt
alphaAlt = do (_, vs, _) <- idR
              andR $ map (alphaAltId Nothing) vs

-----------------------------------------------------------------------

-- | Rename all identifiers bound in a case expression.
alphaCase :: RewriteH CoreExpr
alphaCase = alphaCaseBinder Nothing >+> caseAnyR (fail "") (const alphaAlt)

-----------------------------------------------------------------------

-- | Alpha rename a non-recursive let binder.  Optionally takes a suggested new name.
alphaLetNonRec :: Maybe TH.Name -> RewriteH CoreExpr
alphaLetNonRec mn = do Let (NonRec v _) _ <- idR
                       v' <- freshIdT mn v
                       letNonRecT idR (renameIdR v v') (\ _ e1 e2 -> Let (NonRec v' e1) e2)

-- | Rename the specified identifier bound in a recursive let.  Optionally takes a suggested new name.
alphaLetRecId :: Maybe TH.Name -> Id -> RewriteH CoreExpr
alphaLetRecId mn v = do Let (Rec {}) _ <- idR
                        v' <- freshIdT mn v
                        letRecDefT (\ _ -> renameIdR v v') (renameIdR v v') (\ bs e -> Let (Rec $ (map.first) (replaceId v v') bs) e)

-- | Rename all identifiers bound in a recursive let.
alphaLetRec :: RewriteH CoreExpr
alphaLetRec = do Let (Rec bs) _ <- idR
                 andR $ map (alphaLetRecId Nothing . fst) bs

-- | Rename the identifier bound in a recursive let with a single recursively bound identifier.  Optionally takes a suggested new name.
alphaLetRecOne :: Maybe TH.Name -> RewriteH CoreExpr
alphaLetRecOne mn = do Let (Rec [(v, _)]) _ <- idR
                       alphaLetRecId mn v

-- | Rename the identifier bound in a let with a single bound identifier.  Optionally takes a suggested new name.
alphaLetOne :: Maybe TH.Name -> RewriteH CoreExpr
alphaLetOne mn = alphaLetNonRec mn <+ alphaLetRecOne mn

-- | Rename all identifiers bound in a Let.
alphaLet :: RewriteH CoreExpr
alphaLet = alphaLetRec <+ alphaLetNonRec Nothing

-----------------------------------------------------------------------

-- | Alpha rename a non-recursive top-level binder.  Optionally takes a suggested new name.
alphaConsNonRec :: Maybe TH.Name -> RewriteH CoreProgram
alphaConsNonRec mn = do NonRec v _ : _ <- idR
                        v' <- freshIdT mn v
                        consNonRecT idR (renameIdR v v') (\ _ e1 e2 -> NonRec v' e1 : e2)

-- | Rename the specified identifier bound in a recursive top-level binder.  Optionally takes a suggested new name.
alphaConsRecId :: Maybe TH.Name -> Id -> RewriteH CoreProgram
alphaConsRecId mn v = do Rec {} : _ <- idR
                         v' <- freshIdT mn v
                         consRecDefT (\ _ -> renameIdR v v') (renameIdR v v') (\ bs e -> Rec ((map.first) (replaceId v v') bs) : e)

-- | Rename all identifiers bound in a recursive top-level binder.
alphaConsRec :: RewriteH CoreProgram
alphaConsRec = do Rec bs : _ <- idR
                  andR $ map (alphaConsRecId Nothing . fst) bs

-- | Rename the identifier bound in a recursive top-level binder with a single recursively bound identifier.  Optionally takes a suggested new name.
alphaConsRecOne :: Maybe TH.Name -> RewriteH CoreProgram
alphaConsRecOne mn = do Rec [(v, _)] : _ <- idR
                        alphaConsRecId mn v

-- | Rename the identifier bound in a top-level binder with a single bound identifier.  Optionally takes a suggested new name.
alphaConsOne :: Maybe TH.Name -> RewriteH CoreProgram
alphaConsOne mn = alphaConsNonRec mn <+ alphaConsRecOne mn

-- | Rename all identifiers bound in a Let.
alphaCons :: RewriteH CoreProgram
alphaCons = alphaConsRec <+ alphaConsNonRec Nothing

-----------------------------------------------------------------------

-- | Alpha rename any bindings at this node.  Note: does not rename case alternatives unless invoked on the alternative.
alpha :: RewriteH Core
alpha = setFailMsg "Cannot alpha-rename here." $
           promoteExprR (alphaLam Nothing <+ alphaCaseBinder Nothing <+ alphaLet)
        <+ promoteProgramR alphaCons

-----------------------------------------------------------------------
