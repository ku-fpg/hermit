{-# LANGUAGE FlexibleContexts #-}

module HERMIT.Dictionary.Local
       ( -- * Local Structural Manipulations
         HERMIT.Dictionary.Local.externals
         -- ** Binding Groups
       , module HERMIT.Dictionary.Local.Bind
         -- ** Case Expressions
       , module HERMIT.Dictionary.Local.Case
         -- ** Cast Expressions
       , module HERMIT.Dictionary.Local.Cast
         -- ** Let Expressions
       , module HERMIT.Dictionary.Local.Let
         -- ** Miscellaneous
       , abstractR
       , pushR
       , betaReduceR
       , betaReducePlusR
       , betaExpandR
       , etaReduceR
       , etaExpandR
       , multiEtaExpandR
       , flattenModuleR
       , flattenProgramR
       , flattenProgramT
       )
where

import HERMIT.Core
import HERMIT.Context
import HERMIT.Kure
import HERMIT.Monad
import HERMIT.External
import HERMIT.GHC
import HERMIT.Utilities

import HERMIT.Dictionary.Common
import HERMIT.Dictionary.Local.Bind hiding (externals)
import qualified HERMIT.Dictionary.Local.Bind as Bind
import HERMIT.Dictionary.Local.Case hiding (externals)
import qualified HERMIT.Dictionary.Local.Case as Case
import HERMIT.Dictionary.Local.Cast hiding (externals)
import qualified HERMIT.Dictionary.Local.Cast as Cast
import HERMIT.Dictionary.Local.Let hiding (externals)
import qualified HERMIT.Dictionary.Local.Let as Let

import qualified Language.Haskell.TH as TH

import Control.Arrow

------------------------------------------------------------------------------

-- | Externals for local structural manipulations.
--   (Many taken from Chapter 3 of Andre Santos' dissertation.)
externals :: [External]
externals =
    [ external "beta-reduce" (promoteExprR betaReduceR :: RewriteH Core)
        [ "((\\ v -> E1) E2) ==> let v = E2 in E1"
        , "This form of beta-reduction is safe if E2 is an arbitrary expression"
        , "(won't duplicate work)." ]                                 .+ Eval .+ Shallow
    , external "beta-reduce-plus" (promoteExprR betaReducePlusR :: RewriteH Core)
        [ "Perform one or more beta-reductions."]                               .+ Eval .+ Shallow
    , external "beta-expand" (promoteExprR betaExpandR :: RewriteH Core)
        [ "(let v = e1 in e2) ==> (\\ v -> e2) e1" ]                            .+ Shallow
    , external "eta-reduce" (promoteExprR etaReduceR :: RewriteH Core)
        [ "(\\ v -> e1 v) ==> e1" ]                                             .+ Eval .+ Shallow
    , external "eta-expand" (promoteExprR . etaExpandR . show :: TH.Name -> RewriteH Core)
        [ "\"eta-expand 'v\" performs e1 ==> (\\ v -> e1 v)" ]                  .+ Shallow .+ Introduce
    , external "flatten-module" (promoteModGutsR flattenModuleR :: RewriteH Core)
        [ "Flatten all the top-level binding groups in the module to a single recursive binding group."
        , "This can be useful if you intend to appply GHC RULES." ]
    , external "flatten-program" (promoteProgR flattenProgramR :: RewriteH Core)
        [ "Flatten all the top-level binding groups in a program (list of binding groups) to a single"
        , "recursive binding group.  This can be useful if you intend to apply GHC RULES." ]
    , external "abstract" (promoteExprR . abstractR :: TH.Name -> RewriteH Core)
        [ "Abstract over a variable using a lambda."
        , "e  ==>  (\\ x -> e) x" ]                                             .+ Shallow .+ Introduce .+ Context
    , external "push" ((\ nm strictf -> push (Just strictf) (cmpTHName2Var nm)) :: TH.Name -> RewriteH Core -> RewriteH Core)
        [ "Push a function 'f into a case-expression or let-expression argument,"
        , "given a proof that f (fully saturated with type arguments) is strict." ] .+ Shallow .+ Commute
    , external "push-unsafe" (push Nothing . cmpTHName2Var :: TH.Name -> RewriteH Core)
        [ "Push a function 'f into a case-expression or let-expression argument."
        , "Requires 'f to be strict." ] .+ Shallow .+ Commute .+ PreCondition
    ]
    ++ Bind.externals
    ++ Case.externals
    ++ Cast.externals
    ++ Let.externals

------------------------------------------------------------------------------

-- | @((\\ v -> e1) e2)@ ==> @(let v = e2 in e1)@
--   This form of beta-reduction is safe if e2 is an arbitrary
--   expression (won't duplicate work).
betaReduceR :: MonadCatch m => Rewrite c m CoreExpr
betaReduceR = setFailMsg ("Beta-reduction failed: " ++ wrongExprForm "App (Lam v e1) e2") $
    do App (Lam v e1) e2 <- idR
       return $ Let (NonRec v e2) e1


multiBetaReduceR :: MonadCatch m =>  (Int -> Bool) -> Rewrite c m CoreExpr
multiBetaReduceR p = prefixFailMsg "Multi-Beta-Reduce failed: " $
    do
        e <- idR
        let (f,xs) = collectArgs e
        guardMsg (p (length xs)) "incorrect number of arguments."

        let (vs,e0) = collectBinders f

        guardMsg (length vs >= length xs) "insufficent lambdas."

        let (vs1,vs2) = splitAt (length xs) vs

        return
           $ mkLets (zipWith NonRec vs1 xs)
           $ mkLams vs2 e0

-- TODO: inline this everywhere
-- Neil: Are we sure we want to inline this?
-- | Perform one or more beta-reductions.
betaReducePlusR :: MonadCatch m => Rewrite c m CoreExpr
betaReducePlusR = multiBetaReduceR (> 0)

{-

        tagFailR "betaReducePlus failed." $
        appT liftLambda idR App >>> beta_reduce
  where
          -- lift lambda finds the (perhaps hidden) lambda, and brings it out
          liftLambda = observeR "pre-liftLambda" >>> liftLambda' >>> observeR "post-liftLambda"
          liftLambda' =
                   (do e@(Lam {}) <- idR
                       return e)
                <+ (betaReducePlus
                        >>> observeR "liftLambda(UP)"
                            -- let v = e in ...
                            -- TODO: check scope here
                        >>> (do Let bds (Lam v e) <- idR
                                return (Lam v (Let bds e)))
                   )
-}

-- | (let v = e1 in e2) ==> (\\ v -> e2) e1
betaExpandR :: MonadCatch m => Rewrite c m CoreExpr
betaExpandR = setFailMsg ("Beta-expansion failed: " ++ wrongExprForm "Let (NonRec v e1) e2") $
    do Let (NonRec v e1) e2 <- idR
       return $ App (Lam v e2) e1

------------------------------------------------------------------------------

-- | (\\ v -> f v) ==> f
etaReduceR :: MonadCatch m => Rewrite c m CoreExpr
etaReduceR = prefixFailMsg "Eta-reduction failed: " $
            withPatFailMsg (wrongExprForm "Lam v (App f (Var v))") $
            do Lam v1 (App f e) <- idR
               case e of
                  Var v2  -> guardMsg (v1 == v2) "the expression has the right form, but the variables are not equal."
                  Type ty -> case getTyVar_maybe ty of
                               Nothing -> fail "the argument expression is not a type variable."
                               Just v2 -> guardMsg (v1 == v2) "type variables are not equal."
                  _       -> fail "the argument expression is not a variable."
               guardMsg (v1 `notElemVarSet` freeVarsExpr f) $ var2String v1 ++ " is free in the function being applied."
               return f

-- | e1 ==> (\\ v -> e1 v)
etaExpandR :: String -> Rewrite c HermitM CoreExpr
etaExpandR nm = prefixFailMsg "Eta-expansion failed: " $
               contextfreeT $ \ e -> let ty = exprKindOrType e in
        case splitFunTy_maybe ty of
          Just (argTy, _) -> do v <- newIdH nm argTy
                                return $ Lam v (App e (varToCoreExpr v))
          Nothing         -> case splitForAllTy_maybe ty of
                               Just (tv,_) -> do v <- newTyVarH nm (tyVarKind tv)
                                                 return $ Lam v (App e (varToCoreExpr v))
                               Nothing -> fail "type of expression is not a function or a forall."

-- | Perform multiple eta-expansions.
multiEtaExpandR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c) => [String] -> Rewrite c HermitM CoreExpr
multiEtaExpandR []       = idR
multiEtaExpandR (nm:nms) = etaExpandR nm >>> lamAllR idR (multiEtaExpandR nms)

------------------------------------------------------------------------------

-- | Flatten all the top-level binding groups in the module to a single recursive binding group.
flattenModuleR :: (ExtendPath c Crumb, Monad m) => Rewrite c m ModGuts
flattenModuleR = modGutsR flattenProgramR

-- | Flatten all the top-level binding groups in a program to a program containing a single recursive binding group.
flattenProgramR :: Monad m => Rewrite c m CoreProg
flattenProgramR = do bnd <- flattenProgramT
                     return (bindsToProg [bnd])

-- | Flatten all the top-level binding groups in a program to a single recursive binding group.
flattenProgramT :: Monad m => Translate c m CoreProg CoreBind
flattenProgramT = do bds <- arr (concatMap bindToVarExprs . progToBinds)
                     guardMsg (nodups $ map fst bds) "Top-level bindings contain multiple occurrences of a name."
                     return (Rec bds)

------------------------------------------------------------------------------

-- | Abstract over a variable using a lambda.
--   e  ==>  (\ x. e) x
abstractR :: (ReadBindings c, MonadCatch m) => TH.Name -> Rewrite c m CoreExpr
abstractR nm = prefixFailMsg "abstraction failed: " $
   do e <- idR
      v <- findBoundVarT nm
      return (App (Lam v e) (varToCoreExpr v))

------------------------------------------------------------------------------------------------------

push :: Maybe (RewriteH Core) -- ^ a proof that the function (after being applied to its type arguments) is strict
     -> (Id -> Bool)          -- ^ a predicate to identify the function
     -> RewriteH Core
push mstrict p = promoteExprR (pushR (extractR `fmap` mstrict) p)

-- | Push a function through a Case or Let expression.
--   Unsafe if the function is not strict.
pushR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, ReadBindings c, HasGlobalRdrEnv c)
      => Maybe (Rewrite c HermitM CoreExpr) -- ^ a proof that the function (after being applied to its type arguments) is strict
      -> (Id -> Bool)                       -- ^ a predicate to identify the function
      -> Rewrite c HermitM CoreExpr
pushR strictf p = prefixFailMsg "push failed: " $
                  withPatFailMsg (wrongExprForm "App f e") $
     do App f e <- idR
        case collectArgs f of
          (Var i,args) -> do
                  guardMsg (p i) $ "identifier not matched."
                  guardMsg (all isTypeArg args) $ "initial arguments are not all type arguments."
                  case e of
                     Case {} -> caseFloatArgR (Just (f,strictf))
                     Let {}  -> letFloatArgR
                     _       -> fail "argument is not a Case or Let."
          _ -> fail "no identifier to match."

------------------------------------------------------------------------------------------------------
