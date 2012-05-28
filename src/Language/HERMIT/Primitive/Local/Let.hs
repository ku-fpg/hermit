-- Andre Santos' Local Transformations (Ch 3 in his dissertation)
module Language.HERMIT.Primitive.Local.Let where

import GhcPlugins

import Data.List (nub)
import Control.Applicative

import Language.KURE
import Language.KURE.Injection

import Language.HERMIT.HermitKure
import Language.HERMIT.HermitEnv
import Language.HERMIT.HermitMonad
import Language.HERMIT.External

import Language.HERMIT.Primitive.GHC
import Language.HERMIT.Primitive.Subst

import qualified Language.Haskell.TH as TH

------------------------------------------------------------------------------

externals :: [External]
externals = map (.+ LetCmd) $
         [ external "let-constructor-reuse" (promoteR $ not_defined "constructor-reuse" :: RewriteH Core)
                     [ "let v = C v1..vn in ... C v1..vn ... ==> let v = C v1..vn in ... v ..., fails otherwise" ] .+ Unimplemented
         , external "let-float-app" (promoteR letFloatApp :: RewriteH Core)
                     [ "(let v = ev in e) x ==> let v = ev in e x" ]
         , external "let-float-let" (promoteR letFloatLet :: RewriteH Core)
                     [ "let v = (let w = ew in ev) in e ==> let w = ew in let v = ev in e" ]
         , external "case-float-let" (promoteR caseFloatLet :: RewriteH Core)
                     [ "let v = case ec of alt1 -> e1 in e ==> case ec of alt1 -> let v = e1 in e" ]
         , external "let-to-case" (promoteR letToCase :: RewriteH Core)
                     [ "let v = ev in e ==> case ev of v -> e" ]
         , external "let-to-case-unbox" (promoteR $ not_defined "let-to-case-unbox" :: RewriteH Core)
                     [ "let v = ev in e ==> case ev of C v1..vn -> let v = C v1..vn in e" ] .+ Unimplemented
         ]

not_defined :: String -> RewriteH CoreExpr
not_defined nm = rewrite $ \ c e -> fail $ nm ++ " not implemented!"

letFloatApp :: RewriteH CoreExpr
letFloatApp = do
    App (Let (NonRec v ev) e) x <- idR
    pure $ Let (NonRec v ev) $ App e x

letFloatLet :: RewriteH CoreExpr
letFloatLet = do
    Let (NonRec v (Let (NonRec w ew) ev)) e <- idR
    pure $ Let (NonRec w ew) $ Let (NonRec v ev) e

caseFloatLet :: RewriteH CoreExpr
caseFloatLet = do
    Let (NonRec v (Case s b ty alts)) e <- idR
    pure $ Case s b ty [ (con, ids, Let (NonRec v ec) e) | (con, ids, ec) <- alts]

letToCase :: RewriteH CoreExpr
letToCase = do
    Let (NonRec v ev) e <- idR
    caseBndr <- freshVarT v
    letT (pure ()) (substR v (Var caseBndr)) $ \ () e' -> Case ev caseBndr (varType v) [(DEFAULT, [], e')]
