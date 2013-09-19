{-# LANGUAGE ScopedTypeVariables, FlexibleContexts #-}

module HERMIT.Primitive.Navigation
       ( -- * Navigation
         externals
       , occurrenceOfT
       , bindingOfT
       , bindingGroupOfT
       , rhsOfT
       , parentOfT
       , considerTargets
       , Considerable(..)
       , considerables
       , considerConstructT
       , nthArgPath
       )
where

import Data.Monoid (mempty)

import Control.Arrow (arr)

import HERMIT.Core
import HERMIT.Context
import HERMIT.Kure
import HERMIT.External
import HERMIT.GHC

import HERMIT.Primitive.Navigation.Crumbs

import qualified Language.Haskell.TH as TH

---------------------------------------------------------------------------------------

-- | 'External's involving navigating to named entities.
externals :: [External]
externals = crumbExternals ++ map (.+ Navigation)
            [ external "rhs-of" (rhsOfT . cmpTHName2Var :: TH.Name -> TranslateH Core LocalPathH)
                [ "Find the path to the RHS of the binding of the named variable." ]
            , external "binding-group-of" (bindingGroupOfT . cmpTHName2Var :: TH.Name -> TranslateH CoreTC LocalPathH)
                [ "Find the path to the binding group of the named variable." ]
            , external "binding-of" (bindingOfT . cmpTHName2Var :: TH.Name -> TranslateH CoreTC LocalPathH)
                [ "Find the path to the binding of the named variable." ]
            , external "occurrence-of" (occurrenceOfT . cmpTHName2Var :: TH.Name -> TranslateH CoreTC LocalPathH)
                [ "Find the path to the first occurrence of the named variable." ]

            , external "consider" (bindingOfT . cmpTHName2Var :: TH.Name -> TranslateH CoreTC LocalPathH)
                [ "consider '<v> focuses on the definition of <v>" ] .+ Deprecated .+ TODO

            , external "consider" (considerConstruct :: String -> TranslateH Core LocalPathH)
                [ "consider <c> focuses on the first construct <c>.",
                  recognizedConsiderables]
            , external "arg" (promoteExprT . nthArgPath :: Int -> TranslateH Core LocalPathH)
                [ "arg n focuses on the (n-1)th argument of a nested application." ]

            , external "parent-of" (parentOfT :: TranslateH Core LocalPathH -> TranslateH Core LocalPathH)
                [ "Focus on the parent of another focal point." ]
            , external "parent-of" (parentOfT :: TranslateH CoreTC LocalPathH -> TranslateH CoreTC LocalPathH)
                [ "Focus on the parent of another focal point." ]
            ]

---------------------------------------------------------------------------------------

-- | Discard the last crumb of a non-empty 'LocalPathH'.
parentOfT :: MonadCatch m => Translate c m g LocalPathH -> Translate c m g LocalPathH
parentOfT t = withPatFailMsg "Path points to origin, there is no parent." $
              do SnocPath (_:p) <- t
                 return (SnocPath p)

-----------------------------------------------------------------------

-- | Find the path to the RHS of a binding.
rhsOfT :: (AddBindings c, ExtendPath c Crumb, ReadPath c Crumb, MonadCatch m) => (Var -> Bool) -> Translate c m Core LocalPathH
rhsOfT p = prefixFailMsg ("rhs-of failed: ") $
           do lp <- onePathToT (arr $ bindingOfCore p)
              case lastCrumb lp of
                Just crumb -> case crumb of
                                Rec_Def _     -> return (lp @@ Def_RHS)
                                Let_Bind      -> return (lp @@ NonRec_RHS)
                                ProgCons_Head -> return (lp @@ NonRec_RHS)
                                _             -> fail "does not have a RHS."
                Nothing -> defOrNonRecT successT lastCrumbT (\ () cr -> mempty @@ cr)

-- | Find the path to the binding group of a variable.
bindingGroupOfT :: (AddBindings c, ExtendPath c Crumb, ReadPath c Crumb, MonadCatch m) => (Var -> Bool) -> Translate c m CoreTC LocalPathH
bindingGroupOfT p = prefixFailMsg ("binding-group-of failed: ") $
                    oneNonEmptyPathToT (promoteBindT $ arr $ bindingGroupOf p)

-- | Find the path to the binding of a variable.
bindingOfT :: (AddBindings c, ExtendPath c Crumb, ReadPath c Crumb, MonadCatch m) => (Var -> Bool) -> Translate c m CoreTC LocalPathH
bindingOfT p = prefixFailMsg ("binding-of failed: ") $
               oneNonEmptyPathToT (arr $ bindingOf p)

-- | Find the path to the first occurrence occurrence of a variable.
occurrenceOfT :: (AddBindings c, ExtendPath c Crumb, ReadPath c Crumb, MonadCatch m) => (Var -> Bool) -> Translate c m CoreTC LocalPathH
occurrenceOfT p = prefixFailMsg ("occurrence-of failed: ") $
                  oneNonEmptyPathToT (arr $ occurrenceOf p)

-----------------------------------------------------------------------

bindingGroupOf :: (Var -> Bool) -> CoreBind -> Bool
bindingGroupOf p (NonRec v _) = p v
bindingGroupOf p (Rec defs)   = any (p . fst) defs

-----------------------------------------------------------------------

bindingOf :: (Var -> Bool) -> CoreTC -> Bool
bindingOf p (Core core)              = bindingOfCore p core
bindingOf p (TyCo (TypeCore ty))     = bindingOfType p ty
bindingOf p (TyCo (CoercionCore co)) = bindingOfCoercion p co

bindingOfCore :: (Var -> Bool) -> Core -> Bool
bindingOfCore p (BindCore bnd)  = bindingOfBind p bnd
bindingOfCore p (DefCore def)   = bindingOfDef p def
bindingOfCore p (ExprCore expr) = bindingOfExpr p expr
bindingOfCore p (AltCore alt)   = bindingOfAlt p alt
bindingOfCore _ _               = False

bindingOfBind :: (Var -> Bool) -> CoreBind -> Bool
bindingOfBind p (NonRec v _) = p v
bindingOfBind _ _            = False

bindingOfDef :: (Var -> Bool) -> CoreDef -> Bool
bindingOfDef p (Def v _) = p v

bindingOfExpr :: (Var -> Bool) -> CoreExpr -> Bool
bindingOfExpr p (Lam v _)      = p v
bindingOfExpr p (Case _ w _ _) = p w
bindingOfExpr _ _              = False

bindingOfAlt :: (Var -> Bool) -> CoreAlt -> Bool
bindingOfAlt p (_,vs,_) = any p vs

bindingOfType :: (TyVar -> Bool) -> Type -> Bool
bindingOfType p (ForAllTy v _) = p v
bindingOfType _ _              = False

bindingOfCoercion :: (CoVar -> Bool) -> Coercion -> Bool
bindingOfCoercion p (ForAllCo v _) = p v
bindingOfCoercion _ _              = False

-----------------------------------------------------------------------

occurrenceOf :: (Var -> Bool) -> CoreTC -> Bool
occurrenceOf p (Core (ExprCore e))      = occurrenceOfExpr p e
occurrenceOf p (TyCo (TypeCore ty))     = occurrenceOfType p ty
occurrenceOf p (TyCo (CoercionCore co)) = occurrenceOfCoercion p co
occurrenceOf _ _                        = False

occurrenceOfExpr :: (Var -> Bool) -> CoreExpr -> Bool
occurrenceOfExpr p (Var v)       = p v
occurrenceOfExpr _ _             = False

occurrenceOfType :: (TyVar -> Bool) -> Type -> Bool
occurrenceOfType p (TyVarTy v) = p v
occurrenceOfType _ _           = False

occurrenceOfCoercion :: (CoVar -> Bool) -> Coercion -> Bool
occurrenceOfCoercion p (CoVarCo v) = p v
occurrenceOfCoercion _ _           = False

-----------------------------------------------------------------------

-- | Find the names of all the variables that could be targets of \"consider\".
considerTargets :: forall c m. (ExtendPath c Crumb, AddBindings c, MonadCatch m) => Translate c m Core [String]
considerTargets = allT $ collectT (promoteBindT nonRec <+ promoteDefT def)
    where
      nonRec :: Translate c m CoreBind String
      nonRec = nonRecT (arr var2String) idR const

      def :: Translate c m CoreDef String
      def = defT (arr var2String) idR const

-- | Language constructs that can be zoomed to.
data Considerable = Binding | Definition | CaseAlt | Variable | Literal | Application | Lambda | LetExpr | CaseOf | Casty | Ticky | TypeExpr | CoercionExpr

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

considerConstruct :: (AddBindings c, ExtendPath c Crumb, ReadPath c Crumb, MonadCatch m) => String -> Translate c m Core LocalPathH
considerConstruct str = case string2considerable str of
                          Nothing -> fail $ "Unrecognized construct \"" ++ str ++ "\". " ++ recognizedConsiderables ++ ".  Or did you mean \"consider '" ++ str ++ "\"?"
                          Just c  -> considerConstructT c

-- | Find the path to the first matching construct.
considerConstructT :: (AddBindings c, ExtendPath c Crumb, ReadPath c Crumb, MonadCatch m) => Considerable -> Translate c m Core LocalPathH
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
nthArgPath :: Monad m => Int -> Translate c m CoreExpr LocalPathH
nthArgPath n = contextfreeT $ \ e -> let funCrumbs = appCount e - 1 - n
                                      in if funCrumbs < 0
                                          then fail ("Argument " ++ show n ++ " does not exist.")
                                          else return (SnocPath (replicate funCrumbs App_Fun) @@ App_Arg)

---------------------------------------------------------------------------------------
