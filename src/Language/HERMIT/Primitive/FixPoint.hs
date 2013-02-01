module Language.HERMIT.Primitive.FixPoint where

import GhcPlugins as GHC hiding (varName)

import Control.Arrow

import Language.HERMIT.Core
import Language.HERMIT.Monad
import Language.HERMIT.Kure
import Language.HERMIT.External
import Language.HERMIT.GHC
import Language.HERMIT.ParserCore
import Language.HERMIT.Primitive.GHC
import Language.HERMIT.Primitive.Common
import Language.HERMIT.Primitive.Local
import Language.HERMIT.Primitive.AlphaConversion
import Language.HERMIT.Primitive.New -- TODO: Sort out heirarchy

import qualified Language.Haskell.TH as TH


externals ::  [External]
externals = map ((.+ Experiment) . (.+ TODO))
         [ external "fix-intro" (promoteDefR fixIntro :: RewriteH Core)
                [ "rewrite a recursive binding into a non-recursive binding using fix" ]
         , external "fix-spec" (promoteExprR fixSpecialization :: RewriteH Core)
                [ "specialize a fix with a given argument"] .+ Shallow
         , external "ww-fac" ((\ wrap unwrap -> promoteExprR $ workerWrapperFac wrap unwrap) :: CoreString -> CoreString -> RewriteH Core)
                [ "Worker/Wrapper Factorisation",
                  "For any f :: a -> a, and given wrap :: b -> a and unwrap :: a -> b as arguments, then",
                  "fix f ==> wrap (fix (unwrap . f . wrap))",
                  "Note: the pre-condition  fix (wrap . unwrap . f) == fix f  is expected to hold."
                ] .+ Introduce .+ Context .+ Experiment .+ PreCondition
         , external "ww-fac-test" ((\ wrap unwrap -> promoteExprR $ workerWrapperFacTest wrap unwrap) :: TH.Name -> TH.Name -> RewriteH Core)
                [ "Under construction "
                ] .+ Introduce .+ Context .+ Experiment .+ PreCondition
         , external "ww-split-test" ((\ wrap unwrap -> promoteDefR $ workerWrapperSplitTest wrap unwrap) :: TH.Name -> TH.Name -> RewriteH Core)
                [ "Under construction "
                ] .+ Introduce .+ Context .+ Experiment .+ PreCondition
         ]

fixLocation :: String
fixLocation = "Data.Function.fix"

findFixId :: TranslateH a Id
findFixId = findIdT (TH.mkName fixLocation)

guardIsFixId :: Id -> TranslateH a ()
guardIsFixId v = do fixId <- findFixId
                    guardMsg (v == fixId) (var2String v ++ " does not match " ++ fixLocation)


-- |  f = e   ==>   f = fix (\ f -> e)
fixIntro :: RewriteH CoreDef
fixIntro = prefixFailMsg "Fix introduction failed: " $
           do Def f e <- idR
              fixId   <- findFixId
              constT $ do f' <- cloneVarH id f
                          let coreFix  = App (App (Var fixId) (Type (idType f)))
                              emptySub = mkEmptySubst (mkInScopeSet (exprFreeVars e))
                              sub      = extendSubst emptySub f (Var f')
                          return $ Def f (coreFix (Lam f' (substExpr (text "fixIntro") sub e)))

-- ironically, this is an instance of worker/wrapper itself.

fixSpecialization :: RewriteH CoreExpr
fixSpecialization = do

        -- fix (t::*) (f :: t -> t) (a :: t) :: t
        App (App (App (Var fixId) (Type _)) _) _ <- idR

        guardIsFixId fixId

        let r :: RewriteH CoreExpr
            r = multiEtaExpand [TH.mkName "f",TH.mkName "a"]

            sub :: RewriteH Core
            sub = pathR [0,1] (promoteR r)

        App (App (App (Var fx) (Type t))
                 (Lam _ (Lam v2 (App (App e _) _a2)))
            )
            (Type t2) <- extractR sub -- In normal form now

        constT $ do let t' = applyTy t t2

                    v3 <- newIdH "f" t'
                    v4 <- newTyVarH "a" (tyVarKind v2)

                    -- f' :: \/ a -> T [a] -> (\/ b . T [b])
                    let f' = Lam v4 (Cast (Var v3) (mkUnsafeCo t' (applyTy t (mkTyVarTy v4))))
                        e' = Lam v3 (App (App e f') (Type t2))

                    return $ App (App (Var fx) (Type t')) e'


workerWrapperFac :: CoreString -> CoreString -> RewriteH CoreExpr
workerWrapperFac wrapS unwrapS = do wrapE   <- contextonlyT (parseCore (unCoreString wrapS))
                                    unwrapE <- contextonlyT (parseCore (unCoreString unwrapS))
                                    monomorphicWorkerWrapperFac wrapE unwrapE

workerWrapperFacTest :: TH.Name -> TH.Name -> RewriteH CoreExpr
workerWrapperFacTest wrapNm unwrapNm = do wrapId   <- findBoundVarT wrapNm
                                          unwrapId <- findBoundVarT unwrapNm
                                          monomorphicWorkerWrapperFac (Var wrapId) (Var unwrapId)

workerWrapperSplitTest :: TH.Name -> TH.Name -> RewriteH CoreDef
workerWrapperSplitTest wrapNm unwrapNm = do wrapId   <- findBoundVarT wrapNm
                                            unwrapId <- findBoundVarT unwrapNm
                                            monomorphicWorkerWrapperSplit (Var wrapId) (Var unwrapId)


-- monomorphicWorkerWrapperFac :: Id -> Id -> RewriteH CoreExpr
-- monomorphicWorkerWrapperFac wrapId unwrapId = -- let wrapTy   = idType wrapId
--                                               --     unwrapTy = idType unwrapId
--                                               --     (wrapForallTyVars, wrapMainTy)     = splitForAllTys wrapTy
--                                               --     (unwrapForallTyVars, unwrapMainTy) = splitForAllTys unwrapTy

--                                               -- in  -- In progress: above are not used yet.
--                                                   workerWrapperFac (Var wrapId) (Var unwrapId)
--                                                 -- workerWrapperFac (mkTyApps (Var wrapId)   wrapForallTys)
--                                                 --                  (mkTyApps (Var unwrapId) unwrapForallTys)

-- workerWrapperFac (Var wrapId) (Var unwrapId)
-- splitForAllTys :: Type -> ([TyVar], Type)

-- monomorphicWorkerWrapperSplit :: Id -> Id -> RewriteH CoreDef
-- monomorphicWorkerWrapperSplit wrapId unwrapId = workerWrapperSplit (Var wrapId) (Var unwrapId)

-- substTyWith :: [TyVar] -> [Type] -> Type -> Type
-- mkTyApps  :: Expr b -> [Type]   -> Expr b

-- I assume there are GHC functions to do this, but I can't find them.
-- in progress
-- unifyTyVars :: [TyVar] -- | forall quantified type variables
--             -> Type    -- | type containing forall quantified type variables
--             -> Type    -- | type to unify with
--             -> Maybe [Type]  -- | types that the variables have been unified with
-- unifyTyVars vs tyGen tySpec = let unifyTyVarsAux tyGen tySpec vs
--                                in undefined
--   unifyTyVarsAux :: Type -> Type -> [(TyVar,[Type])] -> Maybe [(TyVar,[Type])]
--   unifyTyVarsAux (TyVarTy v)   t             = match v t
--   unifyTyVarsAux (AppTy s1 s2) (AppTy t1 t2) = match s1 t1 . match s2 t2


-- f      :: a -> a
-- wrap   :: forall x,y..z. b -> a
-- unwrap :: forall p,q..r. a -> b
-- fix tyA f ==> wrap (fix tyB (\ x -> unwrap (f (wrap (Var x)))))
-- Assumes the arguments are monomorphic functions (all type variables have already been applied)
monomorphicWorkerWrapperFac :: CoreExpr -> CoreExpr -> RewriteH CoreExpr
monomorphicWorkerWrapperFac wrapE unwrapE =
  prefixFailMsg "Worker/wrapper Factorisation failed: " $
  withPatFailMsg (wrongExprForm "fix type fun") $
  do App (App (Var fixId) (Type tyA)) f <- idR  -- fix :: forall a. (a -> a) -> a
     guardIsFixId fixId
     case splitFunTy_maybe (exprType wrapE) of
       Nothing            -> fail "type of wrapper is not a function."
       Just (tyB,wrapTyA) -> case splitFunTy_maybe (exprType unwrapE) of
             Nothing                    -> fail "type of unwrapper is not a function."
             Just (unwrapTyA,unwrapTyB) -> do guardMsg (eqType wrapTyA unwrapTyA) ("argument type of unwrapper does not match result type of wrapper.")
                                              guardMsg (eqType unwrapTyB tyB) ("argument type of wrapper does not match result type of unwrapper.")
                                              guardMsg (eqType wrapTyA tyA) ("wrapper/unwrapper types do not match expression type.")
                                              x <- constT (newIdH "x" tyB)
                                              return $ App wrapE
                                                           (App (App (Var fixId) (Type tyB))
                                                                (Lam x (App unwrapE
                                                                            (App f
                                                                                 (App wrapE
                                                                                      (Var x)
                                                                                 )
                                                                            )
                                                                       )
                                                                )
                                                           )


monomorphicWorkerWrapperSplit :: CoreExpr -> CoreExpr -> RewriteH CoreDef
monomorphicWorkerWrapperSplit wrap unwrap =
  let f    = TH.mkName "f"
      w    = TH.mkName "w"
      work = TH.mkName "work"
      fx   = TH.mkName "fix"
   in
      fixIntro >>> defR ( appAllR idR (letIntro f)
                            >>> letFloatArg
                            >>> letAllR idR ( monomorphicWorkerWrapperFac wrap unwrap
                                                >>> appAllR idR (letIntro w)
                                                >>> letFloatArg
                                                >>> letNonRecAllR (unfold fx >>> alphaLetWith [work] >>> extractR simplifyR) idR
                                                >>> letSubstR
                                                >>> letFloatArg
                                            )
                        )
