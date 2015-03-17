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
    , betaExpandR
    , etaReduceR
    , etaExpandR
    , multiEtaExpandR
    , flattenModuleR
    , flattenProgramR
    , flattenProgramT
    ) where

import HERMIT.Core
import HERMIT.Context
import HERMIT.External
import HERMIT.GHC
import HERMIT.Kure
import HERMIT.Monad
import HERMIT.Name
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

import Control.Arrow

------------------------------------------------------------------------------

-- | Externals for local structural manipulations.
--   (Many taken from Chapter 3 of Andre Santos' dissertation.)
externals :: [External]
externals =
    [ external "beta-reduce" (promoteExprR betaReduceR :: RewriteH LCore)
        [ "((\\ v -> E1) E2) ==> let v = E2 in E1"
        , "This form of beta-reduction is safe if E2 is an arbitrary expression"
        , "(won't duplicate work)." ]                                 .+ Eval .+ Shallow
    , external "beta-expand" (promoteExprR betaExpandR :: RewriteH LCore)
        [ "(let v = e1 in e2) ==> (\\ v -> e2) e1" ]                            .+ Shallow
    , external "eta-reduce" (promoteExprR etaReduceR :: RewriteH LCore)
        [ "(\\ v -> e1 v) ==> e1" ]                                             .+ Eval .+ Shallow
    , external "eta-expand" (promoteExprR . etaExpandR :: String -> RewriteH LCore)
        [ "\"eta-expand 'v\" performs e1 ==> (\\ v -> e1 v)" ]                  .+ Shallow .+ Introduce
    , external "flatten-module" (promoteModGutsR flattenModuleR :: RewriteH LCore)
        [ "Flatten all the top-level binding groups in the module to a single recursive binding group."
        , "This can be useful if you intend to appply GHC RULES." ]
    , external "flatten-program" (promoteProgR flattenProgramR :: RewriteH LCore)
        [ "Flatten all the top-level binding groups in a program (list of binding groups) to a single"
        , "recursive binding group.  This can be useful if you intend to apply GHC RULES." ]
    , external "abstract" (promoteExprR . abstractR . mkOccPred :: OccurrenceName -> RewriteH LCore)
        [ "Abstract over a variable using a lambda."
        , "e  ==>  (\\ x -> e) x" ]                                             .+ Shallow .+ Introduce .+ Context
    , external "push" ((\ nm strictf -> push (Just strictf) (cmpString2Var nm)) :: String -> RewriteH LCore -> RewriteH LCore)
        [ "Push a function 'f into a case-expression or let-expression argument,"
        , "given a proof that f (fully saturated with type arguments) is strict." ] .+ Shallow .+ Commute
    , external "push-unsafe" (push Nothing . cmpString2Var :: String -> RewriteH LCore)
        [ "Push a function 'f into a case-expression or let-expression argument."
        , "Requires 'f to be strict." ] .+ Shallow .+ Commute .+ PreCondition .+ Unsafe
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
               guardMsg (v1 `notElemVarSet` freeVarsExpr f) $ unqualifiedName v1 ++ " is free in the function being applied."
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
flattenModuleR :: (ExtendPath c Crumb, HasEmptyContext c, Monad m) => Rewrite c m ModGuts
flattenModuleR = modGutsR flattenProgramR

-- | Flatten all the top-level binding groups in a program to a program containing a single recursive binding group.
flattenProgramR :: Monad m => Rewrite c m CoreProg
flattenProgramR = do bnd <- flattenProgramT
                     return (bindsToProg [bnd])

-- | Flatten all the top-level binding groups in a program to a single recursive binding group.
flattenProgramT :: Monad m => Transform c m CoreProg CoreBind
flattenProgramT = do bds <- arr (concatMap bindToVarExprs . progToBinds)
                     guardMsg (nodups $ map fst bds) "Top-level bindings contain multiple occurrences of a name."
                     return (Rec bds)

------------------------------------------------------------------------------

-- | Abstract over a variable using a lambda.
--   e  ==>  (\ x. e) x
abstractR :: (ReadBindings c, MonadCatch m, MonadUnique m) => (Var -> Bool) -> Rewrite c m CoreExpr
abstractR p = prefixFailMsg "abstraction failed: " $
   do v  <- findBoundVarT p
      v' <- constT (cloneVarH id v) -- currently uses the same visible name (via "id").
                                    -- We could do something else here, e.g. add a prime suffix.
      e  <- arr (substCoreExpr v (varToCoreExpr v'))
      return $ mkCoreApp (Lam v' e) (varToCoreExpr v)

------------------------------------------------------------------------------------------------------

push :: Maybe (RewriteH LCore) -- ^ a proof that the function (after being applied to its type arguments) is strict
     -> (Id -> Bool)          -- ^ a predicate to identify the function
     -> RewriteH LCore
push mstrict p = promoteExprR (pushR (extractR `fmap` mstrict) p)

-- | Push a function through a Case or Let expression.
--   Unsafe if the function is not strict.
pushR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, ReadBindings c)
      => Maybe (Rewrite c HermitM CoreExpr) -- ^ a proof that the function (after being applied to its type arguments) is strict
      -> (Id -> Bool)                       -- ^ a predicate to identify the function
      -> Rewrite c HermitM CoreExpr
pushR mstrictf p = prefixFailMsg "push failed: " $
                   withPatFailMsg (wrongExprForm "App f e") $
     do App f e <- idR
        case collectArgs f of
          (Var i,args) -> do
                  guardMsg (p i) $ "identifier not matched."
                  guardMsg (all isTypeArg args) $ "initial arguments are not all type arguments."
                  case e of
                     Case {} -> caseFloatArgR (Just f) mstrictf
                     Let {}  -> letFloatArgR
                     _       -> fail "argument is not a Case or Let."
          _ -> fail "no identifier to match."

------------------------------------------------------------------------------------------------------
