{-# LANGUAGE ScopedTypeVariables, FlexibleContexts #-}

module Language.HERMIT.Primitive.Navigation
       ( -- * Navigation
         externals
       , bindGroup
       , namedBinding
       , bindingGroupOf
       , considerName
       , rhsOf
       , considerTargets
       , Considerable(..)
       , considerables
       , considerConstructT
       )
where

import Data.Monoid (mempty)

import Control.Arrow (arr)

import GhcPlugins as GHC

import Language.HERMIT.Core
import Language.HERMIT.Context
import Language.HERMIT.Kure
import Language.HERMIT.External
import Language.HERMIT.GHC

import qualified Language.Haskell.TH as TH

---------------------------------------------------------------------------------------

-- | 'External's involving navigating to named entities.
externals :: [External]
externals = map (.+ Navigation)
            [
              external "consider" (considerName :: TH.Name -> TranslateH Core PathH)
                [ "consider '<v> focuses on the definition of <v>" ]
            , external "consider" (considerConstruct :: String -> TranslateH Core PathH)
                [ "consider <c> focuses on the first construct <c>.",
                  recognizedConsiderables]
            , external "rhs-of" (rhsOf :: TH.Name -> TranslateH Core PathH)
                [ "rhs-of '<v> focuses on the right-hand-side of the definition of <v>" ]
            , external "binding-group-of" (bindingGroupOf :: TH.Name -> TranslateH Core PathH)
                [ "binding-group-of '<v> focuses on the binding group that binds the variable <v>" ]
            ]

---------------------------------------------------------------------------------------

-- | Find the path to the RHS of the binding group of the given name.
bindingGroupOf :: MonadCatch m => TH.Name -> Translate c m Core PathH
bindingGroupOf = oneNonEmptyPathToT . bindGroup

-- | Find the path to the definiiton of the provided name.
considerName :: MonadCatch m => TH.Name -> Translate c m Core PathH
considerName = oneNonEmptyPathToT . namedBinding

-- | Find the path to the RHS of the definition of the given name.
rhsOf :: (ExtendPath c Crumb, AddBindings c, ReadPath c Crumb, MonadCatch m) => TH.Name -> Translate c m Core PathH
rhsOf nm = do p  <- onePathToT (namedBinding nm)
              cr <- pathT p (   promoteBindT (nonRecT mempty lastCrumbT $ \ () cr -> cr)
                             <+ promoteDefT  (defT    mempty lastCrumbT $ \ () cr -> cr)
                            )
              return (p ++ [cr])
-- TODO: The new definition is inefficient.  Try and improve it.  May need to generalise the KURE "onePathTo" combinators.
-- rhsOf nm = onePathToT (namedBinding nm) >>^ (++ [0])

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
data Considerable = Binding | Definition | CaseAlt | Variable | Literal | Application | Lambda | LetIn | CaseOf | Casty | Ticky | TypeVar | Coerce

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
                  , ("let",LetIn)
                  , ("case",CaseOf)
                  , ("cast",Casty)
                  , ("tick",Ticky)
                  , ("type",TypeVar)
                  , ("coerce",Coerce)
                  ]

considerConstruct :: MonadCatch m => String -> Translate c m Core PathH
considerConstruct str = case string2considerable str of
                          Nothing -> fail $ "Unrecognized construct \"" ++ str ++ "\". " ++ recognizedConsiderables ++ ".  Or did you mean \"consider '" ++ str ++ "\"?"
                          Just c  -> considerConstructT c

-- | Find the path to the first matching construct.
considerConstructT :: MonadCatch m => Considerable -> Translate c m Core PathH
considerConstructT = oneNonEmptyPathToT . underConsideration

string2considerable :: String -> Maybe Considerable
string2considerable = flip lookup considerables

underConsideration :: Considerable -> Core -> Bool
underConsideration Binding     (BindCore _)               = True
underConsideration Definition  (BindCore (NonRec _ _))    = True
underConsideration Definition  (DefCore _)                = True
underConsideration CaseAlt     (AltCore _)                = True
underConsideration Variable    (ExprCore (Var _))         = True
underConsideration Literal     (ExprCore (Lit _))         = True
underConsideration Application (ExprCore (App _ _))       = True
underConsideration Lambda      (ExprCore (Lam _ _))       = True
underConsideration LetIn       (ExprCore (Let _ _))       = True
underConsideration CaseOf      (ExprCore (Case _ _ _ _))  = True
underConsideration Casty       (ExprCore (Cast _ _))      = True
underConsideration Ticky       (ExprCore (Tick _ _))      = True
underConsideration TypeVar     (ExprCore (Type _))        = True
underConsideration Coerce      (ExprCore (Coercion _))    = True
underConsideration _           _                          = False

---------------------------------------------------------------------------------------
