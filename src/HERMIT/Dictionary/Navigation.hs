{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

module HERMIT.Dictionary.Navigation
    ( -- * Navigation
      externals
    , downT
    , occurrenceOfT
    , bindingOfT
    , bindingGroupOfT
    , rhsOfT
    , parentOfT
    , occurrenceOfTargetsT
    , bindingOfTargetsT
    , bindingGroupOfTargetsT
    , rhsOfTargetsT
    , Considerable(..)
    , considerables
    , considerConstructT
    , nthArgPath
    , string2considerable
    ) where

import Control.Arrow
import Control.Monad

import Data.Dynamic (Typeable)
import Data.Monoid

import HERMIT.Core
import HERMIT.Context
import HERMIT.External
import HERMIT.GHC hiding ((<>))
import HERMIT.Kure
import HERMIT.Name

import HERMIT.Dictionary.Navigation.Crumbs

---------------------------------------------------------------------------------------

-- | 'External's involving navigating to named entities.
externals :: [External]
externals = crumbExternals
    ++ map (.+ Navigation)
        [ external "rhs-of" (rhsOfT . mkRhsOfPred :: RhsOfName -> TransformH Core LocalPathH)
            [ "Find the path to the RHS of the binding of the named variable." ]
        , external "binding-group-of" (bindingGroupOfT . cmpString2Var :: String -> TransformH CoreTC LocalPathH)
            [ "Find the path to the binding group of the named variable." ]
        , external "binding-of" (bindingOfT . mkBindingPred :: BindingName -> TransformH CoreTC LocalPathH)
            [ "Find the path to the binding of the named variable." ]
        , external "occurrence-of" (occurrenceOfT . mkOccPred :: OccurrenceName -> TransformH QC LocalPathH)
            [ "Find the path to the first occurrence of the named variable." ]
        , external "application-of" (applicationOfT . mkOccPred :: OccurrenceName -> TransformH QC LocalPathH)
            [ "Find the path to the first application of the named variable." ]
        , external "consider" (considerConstructT :: Considerable -> TransformH Core LocalPathH)
            [ "consider <c> focuses on the first construct <c>.", recognizedConsiderables ]
        , external "arg" (promoteExprT . nthArgPath :: Int -> TransformH Core LocalPathH)
            [ "arg n focuses on the (n-1)th argument of a nested application." ]
        , external "lams-body" (promoteExprT lamsBodyT :: TransformH Core LocalPathH)
            [ "Descend into the body after a sequence of lambdas." ]
        , external "lets-body" (promoteExprT letsBodyT :: TransformH Core LocalPathH)
            [ "Descend into the body after a sequence of let bindings." ]
        , external "prog-end" (promoteModGutsT gutsProgEndT <+ promoteProgT progEndT :: TransformH Core LocalPathH)
            [ "Descend to the end of a program." ]
        , external "parent-of" (parentOfT :: TransformH Core LocalPathH -> TransformH Core LocalPathH)
            [ "Focus on the parent of another focal point." ]
        , external "parent-of" (parentOfT :: TransformH CoreTC LocalPathH -> TransformH CoreTC LocalPathH)
            [ "Focus on the parent of another focal point." ]
        , external "down" (downT :: TransformH Core LocalPathH)
            [ "Move to the first child."]
        ]

---------------------------------------------------------------------------------------

-- | Discard the last crumb of a non-empty 'LocalPathH'.
parentOfT :: MonadCatch m => Transform c m g LocalPathH -> Transform c m g LocalPathH
parentOfT t = withPatFailMsg "Path points to origin, there is no parent." $
              do SnocPath (_:p) <- t
                 return (SnocPath p)

-----------------------------------------------------------------------

-- | Find the path to the RHS of a binding.
rhsOfT :: (AddBindings c, ExtendPath c Crumb, ReadPath c Crumb, HasEmptyContext c, MonadCatch m) => (Var -> Bool) -> Transform c m Core LocalPathH
rhsOfT p = prefixFailMsg ("rhs-of failed: ") $
           do lp <- onePathToT (arr $ bindingOf p . inject)
              case lastCrumb lp of
                Just crumb -> case crumb of
                                Rec_Def _     -> return (lp @@ Def_RHS)
                                Let_Bind      -> return (lp @@ NonRec_RHS)
                                ProgCons_Head -> return (lp @@ NonRec_RHS)
                                _             -> fail "does not have a RHS."
                Nothing -> defOrNonRecT successT lastCrumbT (\ () cr -> mempty @@ cr)

-- | Find the path to the binding group of a variable.
bindingGroupOfT :: (AddBindings c, ExtendPath c Crumb, ReadPath c Crumb, HasEmptyContext c, MonadCatch m) => (Var -> Bool) -> Transform c m CoreTC LocalPathH
bindingGroupOfT p = prefixFailMsg ("binding-group-of failed: ") $
                    oneNonEmptyPathToT (promoteBindT $ arr $ bindingGroupOf p)

-- | Find the path to the binding of a variable.
bindingOfT :: (AddBindings c, ExtendPath c Crumb, ReadPath c Crumb, HasEmptyContext c, MonadCatch m) => (Var -> Bool) -> Transform c m CoreTC LocalPathH
bindingOfT p = prefixFailMsg ("binding-of failed: ") $
               oneNonEmptyPathToT (arr $ bindingOf p)

-- | Find the path to the first occurrence of a variable.
occurrenceOfT :: (AddBindings c, ExtendPath c Crumb, ReadPath c Crumb, HasEmptyContext c, MonadCatch m)
              => (Var -> Bool) -> Transform c m QC LocalPathH
occurrenceOfT p = prefixFailMsg ("occurrence-of failed: ") $
                  oneNonEmptyPathToT (arr $ occurrenceOf p)

-- | Find the path to an application of a given function.
applicationOfT :: (AddBindings c, ExtendPath c Crumb, HasEmptyContext c, MonadCatch m, ReadPath c Crumb)
               => (Var -> Bool) -> Transform c m QC LocalPathH
applicationOfT p = prefixFailMsg "application-of failed:" $ oneNonEmptyPathToT go
    where go = promoteExprT (appT (extractT go) successT const) <+ arr (occurrenceOf p)

-----------------------------------------------------------------------

bindingGroupOf :: (Var -> Bool) -> CoreBind -> Bool
bindingGroupOf p = any p . bindVars

-----------------------------------------------------------------------

bindingOf :: (Var -> Bool) -> CoreTC -> Bool
bindingOf p = any p . varSetElems . binders

binders :: CoreTC -> VarSet
binders (Core core)              = bindersCore core
binders (TyCo (TypeCore ty))     = binderType ty
binders (TyCo (CoercionCore co)) = binderCoercion co

bindersCore :: Core -> VarSet
bindersCore (BindCore bnd)  = binderBind bnd
bindersCore (DefCore def)   = binderDef def
bindersCore (ExprCore expr) = binderExpr expr
bindersCore (AltCore alt)   = mkVarSet (altVars alt)
bindersCore _               = emptyVarSet

binderBind :: CoreBind -> VarSet
binderBind (NonRec v _) = unitVarSet v
binderBind _            = emptyVarSet

binderDef :: CoreDef -> VarSet
binderDef = unitVarSet . defId

binderExpr :: CoreExpr -> VarSet
binderExpr (Lam v _)      = unitVarSet v
binderExpr (Case _ w _ _) = unitVarSet w
binderExpr _              = emptyVarSet

binderType :: Type -> VarSet
binderType (ForAllTy v _) = unitVarSet v
binderType _              = emptyVarSet

binderCoercion :: Coercion -> VarSet
binderCoercion (ForAllCo v _) = unitVarSet v
binderCoercion _              = emptyVarSet

-----------------------------------------------------------------------

occurrenceOf :: (Var -> Bool) -> QC -> Bool
occurrenceOf p = maybe False p . (projectM >=> varOccurrence)

varOccurrence :: CoreTC -> Maybe Var
varOccurrence (Core (ExprCore e))      = varOccurrenceExpr e
varOccurrence (TyCo (TypeCore ty))     = varOccurrenceType ty
varOccurrence (TyCo (CoercionCore co)) = varOccurrenceCoercion co
varOccurrence _                        = Nothing

varOccurrenceExpr :: CoreExpr -> Maybe Var
varOccurrenceExpr (Var v)       = Just v
varOccurrenceExpr _             = Nothing

varOccurrenceType :: Type -> Maybe Var
varOccurrenceType (TyVarTy v) = Just v
varOccurrenceType _           = Nothing

varOccurrenceCoercion :: Coercion -> Maybe Var
varOccurrenceCoercion (CoVarCo v) = Just v
varOccurrenceCoercion _           = Nothing

-----------------------------------------------------------------------

-- | Find all possible targets of 'occurrenceOfT'.
occurrenceOfTargetsT :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, HasEmptyContext c, MonadCatch m) => Transform c m CoreTC VarSet
occurrenceOfTargetsT = allT $ crushbuT (arr varOccurrence >>> projectT >>^ unitVarSet)

-- | Find all possible targets of 'bindingOfT'.
bindingOfTargetsT :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, HasEmptyContext c, MonadCatch m) => Transform c m CoreTC VarSet
bindingOfTargetsT = allT $ crushbuT (arr binders)

-- | Find all possible targets of 'bindingGroupOfT'.
bindingGroupOfTargetsT :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, HasEmptyContext c, MonadCatch m) => Transform c m CoreTC VarSet
bindingGroupOfTargetsT = allT $ crushbuT (promoteBindT $ arr (mkVarSet . bindVars))

-- | Find all possible targets of 'rhsOfT'.
rhsOfTargetsT :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, HasEmptyContext c, MonadCatch m) => Transform c m CoreTC VarSet
rhsOfTargetsT = crushbuT (promoteBindT (arr binderBind) <+ promoteDefT (arr binderDef))

-----------------------------------------------------------------------

-- | Language constructs that can be zoomed to.
data Considerable = Binding | Definition | CaseAlt | Variable | Literal | Application | Lambda | LetExpr | CaseOf | Casty | Ticky | TypeExpr | CoercionExpr
    deriving Typeable

instance Extern Considerable where
    type Box Considerable = Considerable
    box = id
    unbox = id

recognizedConsiderables :: String
recognizedConsiderables = "Recognized constructs are: " ++ show (map fst considerables)

-- | Lookup table for constructs that can be considered; the keys are the arguments the user can give to the \"consider\" command.
considerables ::  [(String,Considerable)]
considerables =   [ ("bind",Binding)
                  , ("def",Definition)
                  , ("alt",CaseAlt)
                  , ("var",Variable)
                  , ("lit",Literal)
                  , ("app",Application)
                  , ("lam",Lambda)
                  , ("let",LetExpr)
                  , ("case",CaseOf)
                  , ("cast",Casty)
                  , ("tick",Ticky)
                  , ("type",TypeExpr)
                  , ("coerce",CoercionExpr)
                  ]

-- | Find the path to the first matching construct.
considerConstructT :: (AddBindings c, ExtendPath c Crumb, ReadPath c Crumb, HasEmptyContext c, MonadCatch m) => Considerable -> Transform c m Core LocalPathH
considerConstructT con = oneNonEmptyPathToT (arr $ underConsideration con)

string2considerable :: String -> Maybe Considerable
string2considerable = flip lookup considerables

underConsideration :: Considerable -> Core -> Bool
underConsideration Binding      (BindCore _)               = True
underConsideration Definition   (BindCore (NonRec _ _))    = True
underConsideration Definition   (DefCore _)                = True
underConsideration CaseAlt      (AltCore _)                = True
underConsideration Variable     (ExprCore (Var _))         = True
underConsideration Literal      (ExprCore (Lit _))         = True
underConsideration Application  (ExprCore (App _ _))       = True
underConsideration Lambda       (ExprCore (Lam _ _))       = True
underConsideration LetExpr      (ExprCore (Let _ _))       = True
underConsideration CaseOf       (ExprCore (Case _ _ _ _))  = True
underConsideration Casty        (ExprCore (Cast _ _))      = True
underConsideration Ticky        (ExprCore (Tick _ _))      = True
underConsideration TypeExpr     (ExprCore (Type _))        = True
underConsideration CoercionExpr (ExprCore (Coercion _))    = True
underConsideration _            _                          = False

---------------------------------------------------------------------------------------

-- | Construct a path to the (n-1)th argument in a nested sequence of 'App's.
nthArgPath :: Monad m => Int -> Transform c m CoreExpr LocalPathH
nthArgPath n = contextfreeT $ \ e -> let funCrumbs = appCount e - 1 - n
                                      in if funCrumbs < 0
                                          then fail ("Argument " ++ show n ++ " does not exist.")
                                          else return (SnocPath (replicate funCrumbs App_Fun) @@ App_Arg)

---------------------------------------------------------------------------------------

instance HasEmptyContext c => HasEmptyContext (ExtendContext c (LocalPath Crumb)) where
  setEmptyContext :: ExtendContext c (LocalPath Crumb) -> ExtendContext c (LocalPath Crumb)
  setEmptyContext ec = ec { baseContext = setEmptyContext (baseContext ec)
                          , extraContext = mempty }

exhaustRepeatCrumbT :: (AddBindings c, ReadPath c Crumb, ExtendPath c Crumb, HasEmptyContext c, Walker c CoreTC, MonadCatch m) => Crumb -> Transform c m CoreTC LocalPathH
exhaustRepeatCrumbT cr = let l = exhaustPathL (repeat cr)
                          in withLocalPathT (focusT l exposeLocalPathT)

-- | Construct a path to the body of a sequence of lambdas.
lamsBodyT :: (AddBindings c, ReadPath c Crumb, ExtendPath c Crumb, HasEmptyContext c, Walker c CoreTC, MonadCatch m) => Transform c m CoreExpr LocalPathH
lamsBodyT = extractT (exhaustRepeatCrumbT Lam_Body)

-- | Construct a path to the body of a sequence of let bindings.
letsBodyT :: (AddBindings c, ReadPath c Crumb, ExtendPath c Crumb, HasEmptyContext c, Walker c CoreTC, MonadCatch m) => Transform c m CoreExpr LocalPathH
letsBodyT = extractT (exhaustRepeatCrumbT Let_Body)

-- | Construct a path to end of a program.
progEndT :: (AddBindings c, ReadPath c Crumb, ExtendPath c Crumb, HasEmptyContext c, Walker c CoreTC, MonadCatch m) => Transform c m CoreProg LocalPathH
progEndT = extractT (exhaustRepeatCrumbT ProgCons_Tail)

-- | Construct a path to teh end of a program, starting at the 'ModGuts'.
gutsProgEndT :: (AddBindings c, ReadPath c Crumb, ExtendPath c Crumb, HasEmptyContext c, Walker c CoreTC, MonadCatch m) => Transform c m ModGuts LocalPathH
gutsProgEndT = modGutsT progEndT (\ _ p -> (mempty @@ ModGuts_Prog) <> p)

---------------------------------------------------------------------------------------

-- | Path to first child.
downT :: Monad m => Transform c m Core LocalPathH
downT = liftM (mempty @@) $ contextfreeT $ \case
                                GutsCore _              -> return ModGuts_Prog
                                AltCore _               -> return Alt_RHS
                                DefCore _               -> return Def_RHS
                                ProgCore (ProgCons _ _) -> return ProgCons_Head
                                BindCore (NonRec _ _)   -> return NonRec_RHS
                                BindCore (Rec _)        -> return (Rec_Def 0)
                                ExprCore (App _ _)      -> return App_Fun
                                ExprCore (Lam _ _)      -> return Lam_Body
                                ExprCore (Let _ _)      -> return Let_Bind
                                ExprCore (Case _ _ _ _) -> return Case_Scrutinee
                                ExprCore (Cast _ _)     -> return Cast_Expr
                                ExprCore (Tick _ _)     -> return Tick_Expr
                                _                       -> fail ("no children")
