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

import GhcPlugins as GHC

import Language.HERMIT.Core
import Language.HERMIT.Kure
import Language.HERMIT.External
import Language.HERMIT.GHC

import Control.Arrow

import qualified Language.Haskell.TH as TH

---------------------------------------------------------------------------------------

-- | 'External's involving navigating to named entities.
externals :: [External]
externals = map (.+ Navigation)
            [
              external "consider" considerName
                [ "consider '<v> focuses on the definition of <v>" ]
            , external "consider" considerConstruct
                [ "consider <c> focuses on the first construct <c>.",
                  recognizedConsiderables]
            , external "rhs-of" rhsOf
                [ "rhs-of '<v> focuses on the right-hand-side of the definition of <v>" ]
            , external "binding-group-of" bindingGroupOf
                [ "binding-group-of '<v> focuses on the binding group that binds the variable <v>" ]
            ]

---------------------------------------------------------------------------------------

-- | Find the path to the RHS of the binding group of the given name.
bindingGroupOf :: TH.Name -> TranslateH Core Path
bindingGroupOf = oneNonEmptyPathToT . bindGroup

-- | Find the path to the definiiton of the provided name.
considerName :: TH.Name -> TranslateH Core Path
considerName = oneNonEmptyPathToT . namedBinding

-- | Find the path to the RHS of the definition of the given name.
rhsOf :: TH.Name -> TranslateH Core Path
rhsOf nm = onePathToT (namedBinding nm) >>^ (++ [0])

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
considerTargets :: TranslateH Core [String]
considerTargets = allT $ collectT (promoteBindT nonRec <+ promoteDefT def)
    where
      nonRec :: TranslateH CoreBind String
      nonRec = nonRecT (return ()) constUnq

      def :: TranslateH CoreDef String
      def = defT (return ()) constUnq

      constUnq :: Var -> () -> String
      constUnq v () = var2String v

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

considerConstruct :: String -> TranslateH Core Path
considerConstruct str = case string2considerable str of
                          Nothing -> fail $ "Unrecognized construct \"" ++ str ++ "\". " ++ recognizedConsiderables ++ ".  Or did you mean \"consider '" ++ str ++ "\"?"
                          Just c  -> considerConstructT c

-- | Find the 'Path' to the first matching construct.
considerConstructT :: Considerable -> TranslateH Core Path
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
