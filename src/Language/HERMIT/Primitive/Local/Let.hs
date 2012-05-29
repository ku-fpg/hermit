-- Andre Santos' Local Transformations (Ch 3 in his dissertation)
module Language.HERMIT.Primitive.Local.Let where

import GhcPlugins

import Control.Applicative
import Control.Arrow

import Language.KURE
import Language.KURE.Injection

import Language.HERMIT.HermitKure
import Language.HERMIT.HermitMonad
import Language.HERMIT.External

import Language.HERMIT.Primitive.GHC
import Language.HERMIT.Primitive.Subst

import qualified Language.Haskell.TH as TH

------------------------------------------------------------------------------

externals :: [External]
externals = map (.+ LetCmd) $
         [ external "let-intro" (promoteR . letIntro :: TH.Name -> RewriteH Core)
                [ "e => (let v = e in v), name of v is provided" ]
         , external "let-constructor-reuse" (promoteR $ not_defined "constructor-reuse" :: RewriteH Core)
                     [ "let v = C v1..vn in ... C v1..vn ... ==> let v = C v1..vn in ... v ..., fails otherwise" ] .+ Unimplemented .+ Eval
         , external "let-float-app" (promoteR letFloatApp :: RewriteH Core)
                     [ "(let v = ev in e) x ==> let v = ev in e x" ] .+ Eval
         , external "let-float-arg" (promoteR letFloatArg :: RewriteH Core)
                     [ "f (let v = ev in e) ==> let v = ev in f e" ] .+ Eval
         , external "let-float-let" (promoteR letFloatLet <+ promoteR letFloatLetTop :: RewriteH Core)
                     [ "let v = (let w = ew in ev) in e ==> let w = ew in let v = ev in e" ] .+ Eval
         , external "case-float-let" (promoteR caseFloatLet :: RewriteH Core)
                     [ "let v = case ec of alt1 -> e1 in e ==> case ec of alt1 -> let v = e1 in e" ] .+ Eval
         , external "let-to-case" (promoteR letToCase :: RewriteH Core)
                     [ "let v = ev in e ==> case ev of v -> e" ]
         , external "let-to-case-unbox" (promoteR $ not_defined "let-to-case-unbox" :: RewriteH Core)
                     [ "let v = ev in e ==> case ev of C v1..vn -> let v = C v1..vn in e" ] .+ Unimplemented
         ]

not_defined :: String -> RewriteH CoreExpr
not_defined nm = rewrite $ \ c e -> fail $ nm ++ " not implemented!"

letIntro ::  TH.Name -> RewriteH CoreExpr
letIntro nm = rewrite $ \ _ e -> do letvar <- newVarH nm (exprType e)
                                    return $ Let (NonRec letvar e) (Var letvar)

-- includes type variables
bindings :: TranslateH CoreBind [Var]
bindings = recT (\_ -> arr (\(Def v _) -> v)) id
        <+ nonRecT idR (\v _ -> [v])

letFloatApp :: RewriteH CoreExpr
letFloatApp = do
    -- match on App (Let bnds e) x, getting the list of vars bound in bnds and the free vars in x
    (vs, frees) <- appT (letT bindings idR const) freeVarsT (,)
    -- if any of the frees would become bound, alpha the let first
    let letAction = if or (map (`elem` frees) vs) then alphaLet else idR
    appT letAction idR $ \ (Let bnds e) x -> Let bnds $ App e x

letFloatArg :: RewriteH CoreExpr
letFloatArg = do
    App f (Let (NonRec v ev) e) <- idR
    pure $ Let (NonRec v ev) $ App f e

letFloatLet :: RewriteH CoreExpr
letFloatLet = do
    Let (NonRec v (Let (NonRec w ew) ev)) e <- idR
    pure $ Let (NonRec w ew) $ Let (NonRec v ev) e

letFloatLetTop :: RewriteH CoreProgram
letFloatLetTop = do
    (NonRec v (Let (NonRec w ew) ev) : e) <- idR
    pure $ (NonRec w ew) : (NonRec v ev) : e


caseFloatLet :: RewriteH CoreExpr
caseFloatLet = do
    Let (NonRec v (Case s b ty alts)) e <- idR
    pure $ Case s b ty [ (con, ids, Let (NonRec v ec) e) | (con, ids, ec) <- alts]

letToCase :: RewriteH CoreExpr
letToCase = do
    Let (NonRec v ev) e <- idR
    caseBndr <- freshVarT v
    letT (pure ()) (substR v (Var caseBndr)) $ \ () e' -> Case ev caseBndr (varType v) [(DEFAULT, [], e')]
