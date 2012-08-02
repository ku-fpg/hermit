{-# LANGUAGE TypeFamilies, FlexibleInstances #-}

-- Placeholder for new prims
module Language.HERMIT.Primitive.New where

import GhcPlugins as GHC hiding (varName)
--import Convert (thRdrNameGuesses)
-- import OccName(varName)

import Control.Applicative
import Control.Arrow

import Language.HERMIT.Context
import Language.HERMIT.Monad
import Language.HERMIT.Kure
import Language.HERMIT.External
import Language.HERMIT.GHC
import Language.HERMIT.Primitive.GHC
import Language.HERMIT.Primitive.Utils
import Language.HERMIT.Primitive.Local
import Language.HERMIT.Primitive.Local.Case
import Language.HERMIT.Primitive.Inline
-- import Language.HERMIT.Primitive.Debug

import qualified Language.Haskell.TH as TH

-- import Debug.Trace
import MonadUtils (MonadIO) -- GHC's MonadIO

import Data.List(intercalate)

externals ::  [External]
externals = map ((.+ Experiment) . (.+ TODO))
         [ external "info" (info :: TranslateH Core String)
                [ "tell me what you know about this expression or binding" ] .+ Unimplemented
         , external "expr-type" (promoteExprT exprTypeT :: TranslateH Core String)
                [ "display the type of this expression"]
         , external "test" (testQuery :: RewriteH Core -> TranslateH Core String)
                [ "determines if a rewrite could be successfully applied" ]
         , external "fix-intro" (promoteBindR fixIntro :: RewriteH Core)
                [ "rewrite a recursive binding into a non-recursive binding using fix" ]
         , external "fix-spec" (promoteExprR fixSpecialization :: RewriteH Core)
                [ "specialize a fix with a given argument"] .+ Shallow .+ TODO
         , external "number-binder" (exprNumberBinder :: Int -> RewriteH Core)
                [ "add a number suffix onto a (lambda) binding" ]
         , external "auto-number-binder" (autoRenameBinder :: RewriteH Core)
                [ "automatically add a number suffix onto a (lambda) binding" ]
         , external "cleanup-unfold" (promoteExprR cleanupUnfold :: RewriteH Core)
                [ "clean up immeduate nested fully-applied lambdas, from the bottom up"]
         , external "unfold" (promoteExprR . unfold :: TH.Name -> RewriteH Core)
                [ "inline a definition, and apply the arguments; tranditional unfold"]
         , external "unshadow" (unshadow :: RewriteH Core)
                [ "Rename local variable with manifestly unique names (x, x0, x1, ...)"]
         , external "push" (promoteExprR . push :: TH.Name -> RewriteH Core)
                [ "push a function <v> into argument" ]
                        -- TODO: does not work with rules with no arguments
         , external "unfold-rule" ((\ nm -> promoteExprR (rules nm >>> cleanupUnfold)) :: String -> RewriteH Core)
                [ "apply a named GHC rule" ]
         , external "var" (promoteExprT . isVar :: TH.Name -> TranslateH Core ())
                 [ "var '<v> returns True for variable v, and False otherwise.",
                   "Useful in combination with \"when\"." ] .+ Predicate
         -- I've modified "var" to return () rather than being an "idR".
         -- Instead of the old "var v >>> r" you should instead say "when (var v) r".
         , external "case-split" (promoteExprR . caseSplit :: TH.Name -> RewriteH Core)
                [ "case-split 'x"
                , "e ==> case x of C1 vs -> e; C2 vs -> e, where x is free in e" ]
         , external "case-split-inline" (caseSplitInline :: TH.Name -> RewriteH Core)
                [ "Like case-split, but additionally inlines the matched constructor "
                , "applications for all occurances of the named variable." ]
         , external "simplify" (simplifyR :: RewriteH Core)
                [ "innermost (unfold '. <+ beta-reduce-plus <+ safe-let-subst <+ case-reduce <+ dead-code-elimination)" ]
         , external "let-tuple" (promoteExprR . letTupleR :: TH.Name -> RewriteH Core)
                [ "let x = e1 in (let y = e2 in e) ==> let t = (e1,e2) in (let x = fst t in (let y = snd t in e))" ]
         ] ++
         [ external "any-call" (withUnfold :: RewriteH Core -> RewriteH Core)
                [ "any-call (.. unfold command ..) applies an unfold commands to all applications"
                , "preference is given to applications with applications with more arguments"
                ] .+ Deep
         ]


isVar :: TH.Name -> TranslateH CoreExpr ()
isVar nm = varT (cmpTHName2Id nm) >>= guardM

simplifyR :: RewriteH Core
simplifyR = innermostR (promoteExprR (unfold (TH.mkName ".") <+ betaReducePlus <+ safeLetSubstR <+ caseReduce <+ dce))

letTupleR :: TH.Name -> RewriteH CoreExpr
letTupleR nm = do
    Let (NonRec x e1) (Let (NonRec y e2) e) <- idR
    condM (letT (nonRecT (pure ()) const)
                (letT (nonRecT freeVarsT (flip const)) (pure ()) const)
                elem)
          (fail "'x' is used in 'e2'")
          (translate $ \ c _ -> do
                tupleConId <- findId c "(,)"
                fstId <- findId c "Data.Tuple.fst"
                sndId <- findId c "Data.Tuple.snd"
                let e1TyE = Type (exprType e1)
                    e2TyE = Type (exprType e1)
                    rhs = mkCoreApps (Var tupleConId) [e1TyE, e2TyE, e1, e2]
                letId <- newVarH nm (exprType rhs)
                let fstE = mkCoreApps (Var fstId) [e1TyE, e2TyE, Var letId]
                    sndE = mkCoreApps (Var sndId) [e1TyE, e2TyE, Var letId]
                return $ Let (NonRec letId rhs)
                        $ Let (NonRec x fstE)
                         $ Let (NonRec y sndE) e)

-- Others
-- let v = E1 in E2 E3 <=> (let v = E1 in E2) E3
-- let v = E1 in E2 E3 <=> E2 (let v = E1 in E3)

-- A few Queries.

info :: TranslateH Core String
info = translate $ \ c core ->
         let pa       = "Path: " ++ show (contextPath c)
             node     = "Node: " ++ coreNode core
             con      = "Constructor: " ++ coreConstructor core
             expExtra = case core of
                          ExprCore e -> ["Type: " ++ showExprType e] ++
                                        ["Free Variables: " ++ showVars (coreExprFreeVars e)] ++
                                           case e of
                                             Var v -> ["Identifier Info: " ++ showIdInfo v]
                                             _     -> []
                          _          -> []
         in
             return (intercalate "\n" $ [pa,node,con] ++ expExtra)

exprTypeT :: TranslateH CoreExpr String
exprTypeT = arr showExprType

showExprType :: CoreExpr -> String
showExprType = showSDoc . ppr . exprType

showIdInfo :: Id -> String
showIdInfo v = showSDoc $ ppIdInfo v $ idInfo v

coreNode :: Core -> String
coreNode (ModGutsCore _) = "Module"
coreNode (ProgramCore _) = "Program"
coreNode (BindCore _)    = "Binding Group"
coreNode (DefCore _)     = "Recursive Definition"
coreNode (ExprCore _)    = "Expression"
coreNode (AltCore _)     = "Case Alternative"

coreConstructor :: Core -> String
coreConstructor (ModGutsCore _)    = "ModGuts"
coreConstructor (ProgramCore prog) = case prog of
                                       []    -> "[]"
                                       (_:_) -> "(:)"
coreConstructor (BindCore bnd)     = case bnd of
                                       Rec _      -> "Rec"
                                       NonRec _ _ -> "NonRec"
coreConstructor (DefCore _)        = "Def"
coreConstructor (AltCore _)        = "(,,)"
coreConstructor (ExprCore expr)    = case expr of
                                       Var _        -> "Var"
                                       Type _       -> "Type"
                                       Lit _        -> "Lit"
                                       App _ _      -> "App"
                                       Lam _ _      -> "Lam"
                                       Let _ _      -> "Let"
                                       Case _ _ _ _ -> "Case"
                                       Cast _ _     -> "Cast"
                                       Tick _ _     -> "Tick"
                                       Coercion _   -> "Coercion"

testQuery :: RewriteH Core -> TranslateH Core String
testQuery r = f <$> testM r
  where
    f True  = "Rewrite would succeed."
    f False = "Rewrite would fail."

findId :: (MonadUnique m, MonadIO m, MonadThings m) => Context -> String -> m Id
findId c = findIdMG (hermitModGuts c)

findIdMG :: (MonadUnique m, MonadIO m, MonadThings m) => ModGuts -> String -> m Id
findIdMG modguts nm =
    case findNameFromTH (mg_rdr_env modguts) $ TH.mkName nm of
        []  -> fail $ "cannot find " ++ nm
        [n] -> lookupId n
        -- TODO: HACK HACK HACK for getting the (,) constructor
        -- we get back two results, the tycon (,) and the datacon (,)
        -- in that order, so we choose the value-level match
        [_,n] -> lookupId n
        ns  -> fail $ "too many " ++ nm ++ " found:\n" ++ intercalate ", " (map showPpr ns)

 --   liftIO $ print ("VAR", GHC.showSDoc . GHC.ppr $ namedFn)

fixIntro :: RewriteH CoreBind
fixIntro = translate $ \ c e -> case e of
        Rec [(f,e0)] -> do
                fixId <- findId c "Data.Function.fix"

                let coreFix = App (App (Var fixId) (Type (idType f)))

                f' <- cloneId id f

                let emptySub = mkEmptySubst (mkInScopeSet (exprFreeVars e0))
                    sub      = extendSubst emptySub f (Var f')

                return $ NonRec f (coreFix (Lam f' (substExpr (text "fixIntro") sub e0)))
        Rec {}       -> fail "recusive group not suitable"
        NonRec {}    -> fail "Cannot take fix of a non-recusive group"

-- ironically, this is an instance of worker/wrapper itself.

fixSpecialization :: RewriteH CoreExpr
fixSpecialization = do
        fixId <- translate $ \ c _ -> findId c "Data.Function.fix"

        -- fix (t::*) (f :: t -> t) (a :: t) :: t
        App (App (App (Var fx) (Type _)) _) _ <- idR

        guardMsg (fx == fixId) "fixSpecialization only works on fix"

        let rr :: RewriteH CoreExpr
            rr = multiEtaExpand [TH.mkName "f",TH.mkName "a"]

            sub :: RewriteH Core
            sub = pathR [0,1] (promoteR rr)
        -- be careful this does not loop (it should not)
        extractR sub >>> fixSpecialization'


fixSpecialization' :: RewriteH CoreExpr
fixSpecialization' = do
        -- In normal form now
        App (App (App (Var fx) (Type t))
                 (Lam _ (Lam v2 (App (App e _) a2)))
            )
            a <- idR

        let t' = case a of
                   Type t2  -> applyTy t t2
--                   Var  a2  -> mkAppTy t (exprType t2)
--                   mkAppTy t t'


        -- TODO: t2' isn't used anywhere -- which means that a2 is never used ???
        let t2' = case a2 of
                   Type t2  -> applyTy t t2
--                   Var  a2  -> mkAppTy t (exprType t2)
--                   mkAppTy t t'


        v3 <- constT $ newVarH (TH.mkName "f") t' -- (funArgTy t')
        v4 <- constT $ newTypeVarH (TH.mkName "a") (tyVarKind v2)

         -- f' :: \/ a -> T [a] -> (\/ b . T [b])
        let f' = Lam v4  (Cast (Var v3)
                               (mkUnsafeCo t' (applyTy t (mkTyVarTy v4))))
        let e' = Lam v3 (App (App e f') a)

        return $ App (App (Var fx) (Type t')) e'


-- | Case split a free variable in an expression:
--
-- Assume expression e which mentions x :: [a]
--
-- e ==> case x of x
--         [] -> e
--         (a:b) -> e
caseSplit :: TH.Name -> RewriteH CoreExpr
caseSplit nm = do
    frees <- freeIdsT
    contextfreeT $ \ e ->
        case [ i | i <- frees, cmpTHName2Id nm i ] of
            []    -> fail "caseSplit: provided name is not free"
            (i:_) -> do
                let (tycon, tys) = splitTyConApp (idType i)
                    dcs = tyConDataCons tycon
                    aNms = map (:[]) $ cycle ['a'..'z']
                dcsAndVars <- mapM (\dc -> do
                                        as <- sequence [ newVarH (TH.mkName a) ty | (a,ty) <- zip aNms $ dataConInstArgTys dc tys ]
                                        return (dc,as)) dcs
                return $ Case (Var i) i (exprType e) [ (DataAlt dc, as, e) | (dc,as) <- dcsAndVars ]

-- | Like caseSplit, but additionally inlines the constructor applications
-- for each occurance of the named variable.
--
-- > caseSplitInline nm = caseSplit nm >>> anybuR (inlineName nm)
caseSplitInline :: TH.Name -> RewriteH Core
caseSplitInline nm = promoteR (caseSplit nm) >>> anybuR (promoteExprR $ inlineName nm)

{-
exprBinder :: TranslateH CoreExpr [(Id,ContextPath)]
exprBinder = translate $ \ c e -> case e of
        Lam b _            -> return [(b,hermitBindingPath c)]
        Let (NonRec b _) _ -> return [(b,hermitBindingPath c)]
        Let (Rec bds) _    -> return [(b,hermitBindingPath c) | b <- map fst bds ]
        _                  -> return []
-}

exprNumberBinder :: Int -> RewriteH Core
exprNumberBinder n = promoteR (exprRenameBinder (++ show n))
                 >>> childR 0 (promoteR letSubstR)

exprRenameBinder :: (String -> String) -> RewriteH CoreExpr
exprRenameBinder nameMod =
--            (do observeR "exprRenameBinder" >>> fail "observe") <+
            (do Lam b e <- idR
                (b',f) <- constT (cloneIdH nameMod b)
                return $ Lam b' (f e))
         <+ (do Let (NonRec b e0) e1 <- idR
                (b',f) <- constT (cloneIdH nameMod b)
--                traceR $ "new name = " ++ show (nameMod $ getOccString b')
                return $ Let (NonRec b' e0) (f e1))

altRenameBinder :: (String -> String) -> RewriteH CoreAlt
altRenameBinder nameMod =
             do (con,bs,e) <- idR
                (bs',f) <- constT (cloneIdsH nameMod bs)
                return (con,bs',f e)

-- This gives an new version of an Id, with the same info, and a new textual name.
cloneIdH :: (String -> String) -> Id -> HermitM (Id,CoreExpr -> CoreExpr)
cloneIdH nameMod b = do
        b' <- cloneId nameMod b
        return (b', Let (NonRec b (Var b')))

cloneIdsH :: (String -> String) -> [Id] -> HermitM ([Id],CoreExpr -> CoreExpr)
cloneIdsH _       []     = return ([],id)
cloneIdsH nameMod (b:bs) = do
        (b',f)   <- cloneIdH  nameMod b
        (bs',fs) <- cloneIdsH nameMod bs
        return (b':bs',f . fs)


-- Here, success is the successful renaming, but if 'id' works, thats okay.
-- AJG: Gut feel, something not quite right here
-- Fails for non-lambdas.

autoRenameBinder :: RewriteH Core
autoRenameBinder =
        promoteR exprAutoRenameBinder
     <+ promoteR altAutoRenameBinder

exprAutoRenameBinder :: RewriteH CoreExpr
exprAutoRenameBinder =
    (do -- check if lambda
        Lam b _ <- idR
        frees <- childT 0 (promoteT freeVarsT) :: TranslateH CoreExpr [Var]
        bound <- translate $ \ c _ -> return (listBindings c)
        exprRenameBinder (inventNames (filter (/= b) (frees ++ bound))) >>> childR 0 (promoteR letSubstR))
 <+ (do -- check in Let
        Let (NonRec b _) _ <- idR
        frees <- freeVarsT :: TranslateH CoreExpr [Var]
        bound <- translate $ \ c _ -> return (listBindings c)
        exprRenameBinder (inventNames (filter (/= b) (frees ++ bound))) >>> childR 0 (promoteR letSubstR))

altAutoRenameBinder :: RewriteH CoreAlt
altAutoRenameBinder = do
        -- check if alt
        (_,bs,_) <- idR
        frees <- childT 0 (promoteT freeVarsT) :: TranslateH CoreAlt [Var]
        bound <- translate $ \ c _ -> return (listBindings c)
        altRenameBinder (inventNames (filter (`notElem` bs) (frees ++ bound)))
                    >>> childR 0 (letSubstNR (length bs))

-- remove N lets, please
letSubstNR :: Int -> RewriteH Core
letSubstNR 0 = idR
letSubstNR n = childR 1 (letSubstNR (n - 1)) >>> promoteExprR letSubstR

inventNames :: [Id] -> String -> String
-- inventNames curr old | trace (show ("inventNames",names,old)) False = undefined
--    where
--            names = map getOccString curr
inventNames curr old = head
                     [ nm
                     | nm <- old : [ old ++ show uq | uq <- [0..] :: [Int] ]
                     , nm `notElem` names
                     ]
   where
           names = map getOccString curr




-- | cleanupUnfold cleans a unfold operation
--  (for example, an inline or rule application)
-- It is used at the level of the top-redex.
cleanupUnfold :: RewriteH CoreExpr
cleanupUnfold = betaReducePlus >>> safeLetSubstPlusR

unfold :: TH.Name -> RewriteH CoreExpr
unfold nm = translate $ \ env e0 -> do
        let n = appCount e0
        let sub :: RewriteH Core
            sub = pathR (replicate n 0) (promoteR $ inlineName nm)

            sub2 :: RewriteH CoreExpr
            sub2 = extractR sub

        e1 <- apply sub2 env e0

        -- only cleanup if 1 or more arguments
        if n > 0 then apply cleanupUnfold env e1
                 else return e1

-- match in a top-down manner,
withUnfold :: RewriteH Core -> RewriteH Core
withUnfold rr = readerT $ \ e -> case e of
        ExprCore (App {}) -> childR 1 rec >+> (rr <+ childR 0 rec)
        ExprCore (Var {}) -> rr
        _                 -> anyR rec
   where

        rec :: RewriteH Core
        rec = withUnfold rr

-- Makes every 'virtual' shadow disappear.
-- O(n^2) right now
-- Also, only does lambda bound things.
unshadow :: RewriteH Core
unshadow = anytdR (promoteR autoRenameBinder)

--cleanUnfold :: (LensH Core Core -> RewriteH Core) -> RewriteH Core
--cleanUnfold f =

-- push a variable into the expression
push :: TH.Name -> RewriteH CoreExpr
push nm = do
        e <- idR
        case collectArgs e of
          (Var v,args) -> do
                  guardMsg (nm `cmpTHName2Id` v) $ "push did not find name " ++ show nm
                  guardMsg (not $ null args) $ "no argument for " ++ show nm
                  guardMsg (all isTypeArg (init args)) $ "initial arguments are not type arguments for " ++ show nm
                  case last args of
                     Case {} -> caseFloatArg
                     _       -> fail "cannot push, sorry"
          _ -> fail "no function to match for push"
