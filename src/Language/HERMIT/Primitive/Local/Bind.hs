module Language.HERMIT.Primitive.Local.Bind
       ( -- * Rewrites on Binding Groups
         externals
       , nonrecToRecR
       , recToNonrecR
       )
where

import GhcPlugins

import Language.HERMIT.External
import Language.HERMIT.GHC
import Language.HERMIT.Kure

import Language.HERMIT.Primitive.Common
------------------------------------------------------------------------------

-- | Externals for manipulating binding groups.
externals :: [External]
externals =
    [ external "nonrec-to-rec" (promoteBindR nonrecToRecR :: RewriteH Core)
        [ "Convert a non-recursive binding into a recursive binding group with a single definition."
        , "NonRec v e ==> Rec [Def v e]" ]                           .+ Shallow
    , external "rec-to-nonrec" (promoteBindR recToNonrecR :: RewriteH Core)
        [ "Convert a singleton recursive binding into a non-recursive binding group."
        , "Rec [Def v e] ==> NonRec v e,  (v not free in e)" ]       .+ Bash -- This may not need to be in bash, as it's subsumed by occurrence analysis.
    ]

------------------------------------------------------------------------------

-- | @'NonRec' v e@ ==> @'Rec' [(v,e)]@
nonrecToRecR :: MonadCatch m => Rewrite c m CoreBind
nonrecToRecR = prefixFailMsg "Converting non-recursive binding to recursive binding failed: " $
               withPatFailMsg (wrongExprForm "NonRec v e") $
  do NonRec v e <- idR
     guardMsg (isId v) "type variables cannot be defined recursively."
     return $ Rec [(v,e)]

-- | @'Rec' [(v,e)]@ ==> @'NonRec' v e@
recToNonrecR :: MonadCatch m => Rewrite c m CoreBind
recToNonrecR = prefixFailMsg "Converting singleton recursive binding to non-recursive binding failed: " $
               withPatFailMsg (wrongExprForm "Rec [Def v e]") $
  do Rec [(v,e)] <- idR
     guardMsg (v `notElemVarSet` exprFreeIds e) ("'" ++ uqName v ++ " is recursively defined.")
     return (NonRec v e)

------------------------------------------------------------------------------
