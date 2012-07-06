-- TODO: rename as Language.HERMIT.Primitive.Navigation
module Language.HERMIT.Primitive.Consider where

import GhcPlugins as GHC

import Language.HERMIT.Kure
import Language.HERMIT.External
import Language.HERMIT.GHC

import Control.Applicative
import Control.Arrow

import qualified Language.Haskell.TH as TH

externals :: [External]
externals = map (.+ Navigation)
            [
              external "consider" considerName
                [ "consider '<v> focuses on a named binding <v>" ]
            , external "consider" considerConstruct
                [ "consider <c> focuses on the first construct <c>.",
                  recognizedConsiderables]
            , external "rhs-of" rhsOf
                [ "rhs-of 'name focuses into the right-hand-side of binding <v>" ]
            ]

-- focus on a binding group
considerName :: TH.Name -> TranslateH Core Path
considerName = onePathToT . bindGroup

-- find a binding group that contains a name.
-- this is slightly different than namedBinding below,
-- as it will take us to the rec in a let rec, rather than
-- the actual binding. TODO: modify considerName or rhsOf
-- so we only need one of these?
bindGroup :: TH.Name -> Core -> Bool
bindGroup nm (BindCore (NonRec v _))  =  nm `cmpName` idName v
bindGroup nm (BindCore (Rec bds))     =  any (cmpName nm . idName) $ map fst bds
bindGroup _  _                        =  False

-- find a specific binding's rhs.
rhsOf :: TH.Name -> TranslateH Core Path
rhsOf nm = onePathToT (namedBinding nm) >>> arr (++ [0])

-- find a named binding.
namedBinding :: TH.Name -> Core -> Bool
namedBinding nm (BindCore (NonRec v _))  =  nm `cmpName` idName v
namedBinding nm (DefCore (Def v _))      =  nm `cmpName` idName v
namedBinding _  _                        =  False

-- find all the possible targets of consider
considerTargets :: TranslateH Core [String]
considerTargets = collectT (promoteT $ nonRec <+ rec) >>> arr concat
    where nonRec = nonRecT (pure ()) (const . (:[]) . unqualified)
          rec    = recT (const (arr (\(Def v _) -> unqualified v))) id

-- | Get the unqualified name from an Id/Var.
unqualified :: Id -> String
unqualified = checkCompose . reverse . showPpr . idName
    where checkCompose ('.':_) = "."
          checkCompose other   = reverse (takeWhile (/='.') other)
-- TODO: Does GHC provide this?

data Considerable = Binding | Definition | CaseAlt | Variable | Literal | Application | Lambda | LetIn | CaseOf | Casty | Ticky | TypeVar | Coerce

recognizedConsiderables :: String
recognizedConsiderables = "Recognized constructs are: " ++ show (map fst considerables)

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
                          Just c  -> onePathToT (underConsideration c)

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


-- I feel like these two should go somewhere else, but seem to get stuck with dependency cycles when I move them.

-- Hacks till we can find the correct way of doing these.
cmpName :: TH.Name -> Name -> Bool
cmpName = cmpTHName2Name

var :: TH.Name -> RewriteH CoreExpr
var nm = whenM (varT $ \ v -> nm `cmpName` idName v) idR
