-- Andre Santos' Local Transformations (Ch 3 in his dissertation)
module Language.HERMIT.Primitive.Local.Let where

import GhcPlugins

import Data.List

import Language.HERMIT.Kure
import Language.HERMIT.Monad
import Language.HERMIT.External

import Language.HERMIT.Primitive.Common
import Language.HERMIT.Primitive.GHC
import Language.HERMIT.Primitive.Subst

import qualified Language.Haskell.TH as TH

------------------------------------------------------------------------------

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
         , external "let-float-let" (promoteProgramR letFloatLetTop <+ promoteExprR (letFloatLet) :: RewriteH Core)
                     [ "let v = (let w = ew in ev) in e ==> let w = ew in let v = ev in e" ] .+ Commute .+ Shallow .+ Bash
         , external "case-float-let" (promoteExprR caseFloatLet :: RewriteH Core)
                     [ "let v = case ec of alt1 -> e1 in e ==> case ec of alt1 -> let v = e1 in e" ] .+ Commute .+ Shallow .+ Bash
         , external "let-to-case" (promoteExprR letToCase :: RewriteH Core)
                     [ "let v = ev in e ==> case ev of v -> e" ] .+ Commute .+ Shallow .+ PreCondition
         -- , external "let-to-case-unbox" (promoteR $ not_defined "let-to-case-unbox" :: RewriteH Core)
         --             [ "let v = ev in e ==> case ev of C v1..vn -> let v = C v1..vn in e" ] .+ Unimplemented
         ]

-- not_defined :: String -> RewriteH CoreExpr
-- not_defined nm = fail $ nm ++ " not implemented!"

letIntro ::  TH.Name -> RewriteH CoreExpr
letIntro nm = prefixFailMsg "Let introduction failed: " $
              contextfreeT $ \ e -> do letvar <- newVarH nm (exprType e)
                                       return $ Let (NonRec letvar e) (Var letvar)

letFloatApp :: RewriteH CoreExpr
letFloatApp = prefixFailMsg "Let floating from App function failed: " $
  do vs <- appT letVarsT freeVarsT intersect
     let letAction = if null vs then idR else alphaLet
     appT letAction idR $ \ (Let bnds e) x -> Let bnds $ App e x

letFloatArg :: RewriteH CoreExpr
letFloatArg = prefixFailMsg "Let floating from App argument failed: " $
  do vs <- appT freeVarsT letVarsT intersect
     let letAction = if null vs then idR else alphaLet
     appT idR letAction $ \ f (Let bnds e) -> Let bnds $ App f e

letFloatLet :: RewriteH CoreExpr
letFloatLet = prefixFailMsg "Let floating from Let failed: " $
  do vs <- letNonRecT letVarsT freeVarsT (\ _ -> intersect)
     let bdsAction = if null vs then idR else nonRecR alphaLet
     letT bdsAction idR $ \ (NonRec v (Let bds ev)) e -> Let bds $ Let (NonRec v ev) e

letFloatLetTop :: RewriteH CoreProgram
letFloatLetTop = setFailMsg "Let floating to top level failed: program does not have the form: NonRec v (Let (NonRec w ew) ev) : bds" $
  do NonRec v (Let (NonRec w ew) ev) : bds <- idR
     return (NonRec w ew : NonRec v ev : bds)

caseFloatLet :: RewriteH CoreExpr
caseFloatLet = prefixFailMsg "Case floating from Let failed: " $
  do vs <- letNonRecT caseAltVarsT idR (\ letVar caseVars _ -> elem letVar $ concat caseVars)
     let bdsAction = if not vs then idR else (nonRecR alphaCase)
     letT bdsAction idR $ \ (NonRec v (Case s b ty alts)) e -> Case s b ty [ (con, ids, Let (NonRec v ec) e) | (con, ids, ec) <- alts]

letToCase :: RewriteH CoreExpr
letToCase = prefixFailMsg "Converting Let to Case failed: " $
  do Let (NonRec v ev) _ <- idR
     caseBndr <- freshVarT v
     letT (return ()) (substR v (Var caseBndr)) $ \ () e' -> Case ev caseBndr (varType v) [(DEFAULT, [], e')]
