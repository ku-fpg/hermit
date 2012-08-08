-- Andre Santos' Local Transformations (Ch 3 in his dissertation)
module Language.HERMIT.Primitive.Local.Let
       ( -- * Rewrites on Let Expressions
         externals
       , letIntro
       , letFloatApp
       , letFloatArg
       , letFloatLet
       , letFloatExpr
       , letFloatLetTop
       , letToCase
       )
where

import GhcPlugins

import Data.List
import Data.Monoid

import Language.HERMIT.Kure
import Language.HERMIT.Monad
import Language.HERMIT.External

import Language.HERMIT.Primitive.Common
import Language.HERMIT.Primitive.GHC hiding (externals)
import Language.HERMIT.Primitive.Subst hiding (externals)

import qualified Language.Haskell.TH as TH

------------------------------------------------------------------------------

-- | Externals relating to Let expressions.
externals :: [External]
externals =
         [ external "let-intro" (promoteExprR . letIntro :: TH.Name -> RewriteH Core)
                [ "e => (let v = e in v), name of v is provided" ]                      .+ Shallow .+ Introduce
         -- , external "let-constructor-reuse" (promoteR $ not_defined "constructor-reuse" :: RewriteH Core)
         --             [ "let v = C v1..vn in ... C v1..vn ... ==> let v = C v1..vn in ... v ..., fails otherwise" ] .+ Unimplemented .+ Eval
         , external "let-float-app" (promoteExprR letFloatApp :: RewriteH Core)
                     [ "(let v = ev in e) x ==> let v = ev in e x" ]                    .+ Commute .+ Shallow .+ Bash
         , external "let-float-arg" (promoteExprR letFloatArg :: RewriteH Core)
                     [ "f (let v = ev in e) ==> let v = ev in f e" ]                    .+ Commute .+ Shallow .+ Bash
         , external "let-float-let" (promoteProgramR letFloatLetTop <+ promoteExprR letFloatLet :: RewriteH Core)
                     [ "let v = (let w = ew in ev) in e ==> let w = ew in let v = ev in e" ] .+ Commute .+ Shallow .+ Bash
         , external "let-float" (promoteProgramR letFloatLetTop <+ promoteExprR letFloatExpr :: RewriteH Core)
                     [ "Float a Let whatever the context." ] .+ Commute .+ Shallow .+ Bash
         , external "let-to-case" (promoteExprR letToCase :: RewriteH Core)
                     [ "let v = ev in e ==> case ev of v -> e" ] .+ Commute .+ Shallow .+ PreCondition
         -- , external "let-to-case-unbox" (promoteR $ not_defined "let-to-case-unbox" :: RewriteH Core)
         --             [ "let v = ev in e ==> case ev of C v1..vn -> let v = C v1..vn in e" ] .+ Unimplemented
         ]

-- not_defined :: String -> RewriteH CoreExpr
-- not_defined nm = fail $ nm ++ " not implemented!"

-- | e => (let v = e in v), name of v is provided
letIntro ::  TH.Name -> RewriteH CoreExpr
letIntro nm = prefixFailMsg "Let introduction failed: " $
              contextfreeT $ \ e -> do letvar <- newVarH (show nm) (exprType e)
                                       return $ Let (NonRec letvar e) (Var letvar)

-- | (let v = ev in e) x ==> let v = ev in e x
letFloatApp :: RewriteH CoreExpr
letFloatApp = prefixFailMsg "Let floating from App function failed: " $
  do vs <- appT letVarsT freeVarsT intersect
     let letAction = if null vs then idR else alphaLet
     appT letAction idR $ \ (Let bnds e) x -> Let bnds $ App e x

-- | f (let v = ev in e) ==> let v = ev in f e
letFloatArg :: RewriteH CoreExpr
letFloatArg = prefixFailMsg "Let floating from App argument failed: " $
  do vs <- appT freeVarsT letVarsT intersect
     let letAction = if null vs then idR else alphaLet
     appT idR letAction $ \ f (Let bnds e) -> Let bnds $ App f e

-- let v = (let w = ew in ev) in e ==> let w = ew in let v = ev in e
letFloatLet :: RewriteH CoreExpr
letFloatLet = prefixFailMsg "Let floating from Let failed: " $
  do vs <- letNonRecT letVarsT freeVarsT (\ _ -> intersect)
     let bdsAction = if null vs then idR else nonRecR alphaLet
     letT bdsAction idR $ \ (NonRec v (Let bds ev)) e -> Let bds $ Let (NonRec v ev) e

-- | Float a Let through an expression, whatever the context.
letFloatExpr :: RewriteH CoreExpr
letFloatExpr = setFailMsg "Unsuitable expression for Let floating." $
               letFloatApp <+ letFloatArg <+ letFloatLet

-- | NonRec v (Let (NonRec w ew) ev) : bds ==> NonRec w ew : NonRec v ev : bds
letFloatLetTop :: RewriteH CoreProgram
letFloatLetTop = setFailMsg ("Let floating to top level failed: " ++ wrongExprForm "NonRec v (Let (NonRec w ew) ev) : bds") $
  do NonRec v (Let (NonRec w ew) ev) : bds <- idR
     return (NonRec w ew : NonRec v ev : bds)

-- | let v = ev in e ==> case ev of v -> e
letToCase :: RewriteH CoreExpr
letToCase = prefixFailMsg "Converting Let to Case failed: " $
  do Let (NonRec v ev) _ <- idR
     nameModifier <- freshNameGen Nothing
     caseBndr <- constT (cloneIdH nameModifier v)
     letT mempty (renameIdR v caseBndr) $ \ () e' -> Case ev caseBndr (varType v) [(DEFAULT, [], e')]
