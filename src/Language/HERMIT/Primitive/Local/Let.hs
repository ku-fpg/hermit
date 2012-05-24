-- Andre Santos' Local Transformations (Ch 3 in his dissertation)
module Language.HERMIT.Primitive.Local.Let where

import GhcPlugins

import Data.List (nub)
import Control.Applicative

import Language.KURE

import Language.HERMIT.HermitKure
import Language.HERMIT.HermitEnv
import Language.HERMIT.HermitMonad
import Language.HERMIT.External

import Language.HERMIT.Primitive.GHC

import qualified Language.Haskell.TH as TH

------------------------------------------------------------------------------

externals :: [External]
externals =
         [ external "let-inline" (promoteR $ not_defined "let-inline")
                     [ "let x = E1 in ...x... ==> let x = E1 in ...E1..., fails otherwise" ] .+ Experiment
         , external "let-constructor-reuse" (promoteR $ not_defined "constructor-reuse")
                     [ "let v = C v1..vn in ... C v1..vn ... ==> let v = C v1..vn in ... v ..., fails otherwise" ] .+ Experiment
         , external "let-float-app" (promoteR $ not_defined "let-float-app")
                     [ "(let v = ev in e) x ==> let v = ev in e x" ] .+ Experiment
         , external "let-float-let" (promoteR $ not_defined "let-float-let")
                     [ "let v = (let w = ew in ev) in e ==> let w = ew in let v = ev in e" ] .+ Experiment
         , external "case-float-let" (promoteR $ not_defined "case-float-let")
                     [ "let v = case ec of alt1 -> e1 in e ==> case ec of alt1 -> let v = e1 in e" ] .+ Experiment
         , external "let-to-case" (promoteR $ not_defined "let-to-case")
                     [ "let v = ev in e ==> case ev of v -> e" ] .+ Experiment
         , external "let-to-case-unbox" (promoteR $ not_defined "let-to-case-unbox")
                     [ "let v = ev in e ==> case ev of C v1..vn -> let v = C v1..vn in e" ] .+ Experiment
         ]

not_defined :: String -> RewriteH CoreExpr
not_defined nm = rewrite $ \ c e -> fail $ nm ++ " not implemented!"

