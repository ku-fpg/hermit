{-# LANGUAGE FlexibleContexts #-}

module HERMIT.Primitive.Local
       ( -- * Local Structural Manipulations
         HERMIT.Primitive.Local.externals
         -- ** Binding Groups
       , module HERMIT.Primitive.Local.Bind
         -- ** Case Expressions
       , module HERMIT.Primitive.Local.Case
         -- ** Cast Expressions
       , module HERMIT.Primitive.Local.Cast
         -- ** Let Expressions
       , module HERMIT.Primitive.Local.Let
         -- ** Miscellaneous
       , abstract
       , push
       , betaReduce
       , betaReducePlus
       , betaExpand
       , etaReduce
       , etaExpand
       , multiEtaExpand
       , flattenModule
       , flattenProgramR
       , flattenProgramT
       )
where

import GhcPlugins

import HERMIT.Core
import HERMIT.Context
import HERMIT.Kure
import HERMIT.Monad
import HERMIT.External
import HERMIT.GHC

import HERMIT.Primitive.Common
import HERMIT.Primitive.Local.Bind hiding (externals)
import qualified HERMIT.Primitive.Local.Bind as Bind
import HERMIT.Primitive.Local.Case hiding (externals)
import qualified HERMIT.Primitive.Local.Case as Case
import HERMIT.Primitive.Local.Cast hiding (externals)
import qualified HERMIT.Primitive.Local.Cast as Cast
import HERMIT.Primitive.Local.Let hiding (externals)
import qualified HERMIT.Primitive.Local.Let as Let

import qualified Language.Haskell.TH as TH

import Control.Arrow

------------------------------------------------------------------------------

-- | Externals for local structural manipulations.
--   (Many taken from Chapter 3 of Andre Santos' dissertation.)
externals :: [External]
externals =
    [ external "beta-reduce" (promoteExprR betaReduce :: RewriteH Core)
        [ "((\\ v -> E1) E2) ==> let v = E2 in E1"
        , "This form of beta-reduction is safe if E2 is an arbitrary expression"
        , "(won't duplicate work)." ]                                 .+ Eval .+ Shallow
    , external "beta-reduce-plus" (promoteExprR betaReducePlus :: RewriteH Core)
        [ "Perform one or more beta-reductions."]                               .+ Eval .+ Shallow .+ Bash
    , external "beta-expand" (promoteExprR betaExpand :: RewriteH Core)
        [ "(let v = e1 in e2) ==> (\\ v -> e2) e1" ]                            .+ Shallow
    , external "eta-reduce" (promoteExprR etaReduce :: RewriteH Core)
        [ "(\\ v -> e1 v) ==> e1" ]                                             .+ Eval .+ Shallow .+ Bash
    , external "eta-expand" (promoteExprR . etaExpand . show :: TH.Name -> RewriteH Core)
        [ "\"eta-expand 'v\" performs e1 ==> (\\ v -> e1 v)" ]                  .+ Shallow .+ Introduce
    , external "flatten-module" (promoteModGutsR flattenModule :: RewriteH Core)
        [ "Flatten all the top-level binding groups in the module to a single recursive binding group."
        , "This can be useful if you intend to appply GHC RULES." ]
    , external "flatten-program" (promoteProgR flattenProgramR :: RewriteH Core)
        [ "Flatten all the top-level binding groups in a program (list of binding groups) to a single"
        , "recursive binding group.  This can be useful if you intend to apply GHC RULES." ]
    , external "abstract" (promoteExprR . abstract :: TH.Name -> RewriteH Core)
        [ "Abstract over a variable using a lambda."
        , "e  ==>  (\\ x -> e) x" ]                                             .+ Shallow .+ Introduce .+ Context
    , external "push" (promoteExprR . push :: TH.Name -> RewriteH Core)
        [ "Push a function 'f into a case-expression or let-expression argument."
        , "Unsafe if 'f is not strict." ] .+ Shallow .+ Commute .+ PreCondition
    ]
    ++ Bind.externals
    ++ Case.externals
    ++ Cast.externals
    ++ Let.externals

------------------------------------------------------------------------------

-- | @((\\ v -> e1) e2)@ ==> @(let v = e2 in e1)@
--   This form of beta-reduction is safe if e2 is an arbitrary
--   expression (won't duplicate work).
betaReduce :: MonadCatch m => Rewrite c m CoreExpr
betaReduce = setFailMsg ("Beta-reduction failed: " ++ wrongExprForm "App (Lam v e1) e2") $
    do App (Lam v e1) e2 <- idR
       return $ Let (NonRec v e2) e1


multiBetaReduce :: MonadCatch m =>  (Int -> Bool) -> Rewrite c m CoreExpr
multiBetaReduce p = prefixFailMsg "Multi-Beta-Reduce failed: " $
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
betaReducePlus :: MonadCatch m => Rewrite c m CoreExpr
betaReducePlus = multiBetaReduce (> 0)

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
betaExpand :: MonadCatch m => Rewrite c m CoreExpr
betaExpand = setFailMsg ("Beta-expansion failed: " ++ wrongExprForm "Let (NonRec v e1) e2") $
    do Let (NonRec v e1) e2 <- idR
       return $ App (Lam v e2) e1

------------------------------------------------------------------------------

-- | (\\ v -> e1 v) ==> e1
etaReduce :: MonadCatch m => Rewrite c m CoreExpr
etaReduce = prefixFailMsg "Eta-reduction failed: " $
            withPatFailMsg (wrongExprForm "Lam v1 (App f e)") $
            do Lam v1 (App f e) <- idR
               case e of
                  Var v2  -> guardMsg (v1 == v2) "the expression has the right form, but the variables are not equal."
                  Type ty -> case getTyVar_maybe ty of
                               Nothing -> fail "the argument expression is not a type variable."
                               Just v2 -> guardMsg (v1 == v2) "type variables are not equal."
                  _       -> fail "the argument expression is not a variable."
               guardMsg (v1 `notElemVarSet` exprFreeIds f) $ var2String v1 ++ " is free in the function being applied."
               return f

-- | e1 ==> (\\ v -> e1 v)
etaExpand :: String -> Rewrite c HermitM CoreExpr
etaExpand nm = prefixFailMsg "Eta-expansion failed: " $
               contextfreeT $ \ e -> let ty = exprType e in
        case splitFunTy_maybe ty of
          Just (argTy, _) -> do v <- newIdH nm argTy
                                return $ Lam v (App e (varToCoreExpr v))
          Nothing         -> case splitForAllTy_maybe ty of
                               Just (tv,_) -> do v <- newTyVarH nm (tyVarKind tv)
                                                 return $ Lam v (App e (varToCoreExpr v))
                               Nothing -> fail "type of expression is not a function or a forall."

-- | Perform multiple eta-expansions.
multiEtaExpand :: (ExtendPath c Crumb, AddBindings c) => [String] -> Rewrite c HermitM CoreExpr
multiEtaExpand []       = idR
multiEtaExpand (nm:nms) = etaExpand nm >>> lamAllR idR (multiEtaExpand nms)

------------------------------------------------------------------------------

-- | Flatten all the top-level binding groups in the module to a single recursive binding group.
flattenModule :: (ExtendPath c Crumb, Monad m) => Rewrite c m ModGuts
flattenModule = modGutsR flattenProgramR

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
abstract :: (ReadBindings c, MonadCatch m) => TH.Name -> Rewrite c m CoreExpr
abstract nm = prefixFailMsg "abstraction failed: " $
   do e <- idR
      v <- findBoundVarT nm
      return (App (Lam v e) (varToCoreExpr v))

------------------------------------------------------------------------------------------------------

-- | Push a function through a Case or Let expression.
--   Unsafe if the function is not strict.
push :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => TH.Name -> Rewrite c HermitM CoreExpr
push nm = prefixFailMsg "push failed: " $
     do e <- idR
        case collectArgs e of
          (Var v,args) -> do
                  guardMsg (nm `cmpTHName2Var` v) $ "cannot find name " ++ show nm
                  guardMsg (not $ null args) $ "no argument for " ++ show nm
                  guardMsg (all isTypeArg $ init args) $ "initial arguments are not type arguments for " ++ show nm
                  case last args of
                     Case {} -> caseFloatArg
                     Let {}  -> letFloatArg
                     _       -> fail "argument is not a Case or Let."
          _ -> fail "no function to match."

------------------------------------------------------------------------------------------------------