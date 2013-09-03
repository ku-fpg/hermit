{-# LANGUAGE ScopedTypeVariables, FlexibleContexts #-}

module HERMIT.Primitive.Navigation
       ( -- * Navigation
         externals
       , bindGroup
       , namedBinding
       , bindingGroupOf
       , considerName
       , rhsOf
       , parentOf
       , considerTargets
       , Considerable(..)
       , considerables
       , considerConstructT
       , nthArgPath
       )
where

import Data.Monoid (mempty)

import Control.Arrow (arr, (>>>))

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
            [
              external "consider" (considerName :: TH.Name -> TranslateH Core LocalPathH)
                [ "consider '<v> focuses on the definition of <v>" ]
            , external "consider" (considerConstruct :: String -> TranslateH Core LocalPathH)
                [ "consider <c> focuses on the first construct <c>.",
                  recognizedConsiderables]
            , external "rhs-of" (rhsOf :: TH.Name -> TranslateH Core LocalPathH)
                [ "rhs-of '<v> focuses on the right-hand-side of the definition of <v>" ]
            , external "binding-group-of" (bindingGroupOf :: TH.Name -> TranslateH Core LocalPathH)
                [ "binding-group-of '<v> focuses on the binding group that binds the variable <v>" ]
            , external "arg" (promoteExprT . nthArgPath :: Int -> TranslateH Core LocalPathH)
                [ "arg n focuses on the (n-1)th argument of a nested application." ]
            , external "parent-of" (parentOf :: TranslateH Core LocalPathH -> TranslateH Core LocalPathH)
                [ "focus on the parent of another focal point." ]
            ]

---------------------------------------------------------------------------------------

-- | Discard the last crumb of a non-empty 'LocalPathH'.
parentOf :: MonadCatch m => Translate c m g LocalPathH -> Translate c m g LocalPathH
parentOf t = withPatFailMsg "Path points to origin, there is no parent." $
             do SnocPath (_:p) <- t
                return (SnocPath p)

-- | Find the path to the RHS of the binding group of the given name.
bindingGroupOf :: (AddBindings c, ExtendPath c Crumb, ReadPath c Crumb, MonadCatch m) => TH.Name -> Translate c m Core LocalPathH
bindingGroupOf nm = setFailMsg ("Binding group for \"" ++ show nm ++ "\" not found.") $ oneNonEmptyPathToT (arr $ bindGroup nm)

-- | Find the path to the definition of the provided name.
considerName :: (AddBindings c, ExtendPath c Crumb, ReadPath c Crumb, MonadCatch m) => TH.Name -> Translate c m Core LocalPathH
considerName nm = setFailMsg ("Definition for \"" ++ show nm ++ "\" not found.") $ oneNonEmptyPathToT (arr $ namedBinding nm)

-- | Find the path to the RHS of the definition of the given name.
rhsOf :: (ExtendPath c Crumb, AddBindings c, ReadPath c Crumb, MonadCatch m) => TH.Name -> Translate c m Core LocalPathH
rhsOf nm = setFailMsg ("Definition for \"" ++ show nm ++ "\" not found.") $ withLocalPathT $ onetdT $
             accepterR (liftContext baseContext (arr $ namedBinding nm)) >>> defOrNonRecT mempty exposeLocalPathT (\ () p -> p)

-- | Verify that this is a binding group defining the given name.
bindGroup :: TH.Name -> Core -> Bool
bindGroup nm (BindCore (NonRec v _))  =  nm `cmpTHName2Var` v
bindGroup nm (BindCore (Rec bds))     =  any (cmpTHName2Var nm . fst) bds
bindGroup _  _                        =  False

-- | Verify that this is the definition of the given name.
namedBinding :: TH.Name -> Core -> Bool
namedBinding nm (BindCore (NonRec v _))  =  nm `cmpTHName2Var` v
namedBinding nm (DefCore (Def v _))      =  nm `cmpTHName2Var` v
namedBinding _  _                        =  False

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
