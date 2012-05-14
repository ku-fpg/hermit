module Language.HERMIT.Primitive.Inline where

import GhcPlugins

import Language.KURE

import Language.HERMIT.HermitKure
import Language.HERMIT.HermitEnv
import Language.HERMIT.External

externals :: [External]
externals = [ 
              external "inline" (promoteR inline)
                [ "(Var n) ==> <defn of n>, fails otherwise" ]
            ]  

-- | The implementation of inline, an important transformation.
-- This *only* works on a Var of the given name. It can trivially
-- be prompted to more general cases.

inline :: RewriteH CoreExpr
inline = rewrite $ \ c e -> case e of
    Var n0 -> -- A candiate for inlining
              case lookupHermitBinding n0 c of
                Nothing       -> fail $ "inline failed, cannot find " ++ show n0 ++ "  in Env"
                Just (LAM {}) -> fail $ "inline failed, found lambda-bound value or type"
                Just (BIND depth _ e')
                  -- need to check for clashes, based on the depth
                  -- for now, just accept, and proceeded
                  -> return e'
    _      -> fail "inline failed (No variable)"
