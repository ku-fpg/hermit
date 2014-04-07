{-# LANGUAGE FlexibleContexts, ScopedTypeVariables #-}

module HERMIT.Dictionary.Kure
       ( -- * KURE Strategies
         externals
       , anyCallR
       )
where

import Control.Arrow
import Control.Monad (liftM)

import HERMIT.Core
import HERMIT.Context
import HERMIT.GHC
import HERMIT.Kure
import HERMIT.External

------------------------------------------------------------------------------------

-- | -- This list contains reflections of the KURE strategies as 'External's.
externals :: [External]
externals = map (.+ KURE)
   [ external "id"         (idR :: RewriteH Core)
       [ "Perform an identity rewrite."] .+ Shallow
   , external "success"    (successT :: TranslateH Core ())
       [ "An always succeeding translation." ]
   , external "fail"       (fail :: String -> RewriteH Core)
       [ "A failing rewrite."]
   , external "<+"         ((<+) :: RewriteH Core -> RewriteH Core -> RewriteH Core)
       [ "Perform the first rewrite, and then, if it fails, perform the second rewrite." ]
   , external "<+"         ((<+) :: TranslateH Core () -> TranslateH Core () -> TranslateH Core ())
       [ "Perform the first check, and then, if it fails, perform the second check." ]
   , external ">>>"        ((>>>) :: RewriteH Core -> RewriteH Core -> RewriteH Core)
       [ "Compose rewrites, requiring both to succeed." ]
   , external ">>>"        ((>>>) :: BiRewriteH Core -> BiRewriteH Core -> BiRewriteH Core)
       [ "Compose bidirectional rewrites, requiring both to succeed." ]
   , external ">+>"        ((>+>) :: RewriteH Core -> RewriteH Core -> RewriteH Core)
       [ "Compose rewrites, allowing one to fail." ]
   , external "try"        (tryR :: RewriteH Core -> RewriteH Core)
       [ "Try a rewrite, and perform the identity if the rewrite fails." ]
   , external "repeat"     (repeatR :: RewriteH Core -> RewriteH Core)
       [ "Repeat a rewrite until it would fail." ] .+ Loop
   , external "replicate"  ((\ n -> andR . replicate n)  :: Int -> RewriteH Core -> RewriteH Core)
       [ "Repeat a rewrite n times." ]
   , external "all"        (allR :: RewriteH Core -> RewriteH Core)
       [ "Apply a rewrite to all children of the node, requiring success at every child." ] .+ Shallow
   , external "any"        (anyR :: RewriteH Core -> RewriteH Core)
       [ "Apply a rewrite to all children of the node, requiring success for at least one child." ] .+ Shallow
   , external "one"        (oneR :: RewriteH Core -> RewriteH Core)
       [ "Apply a rewrite to the first child of the node for which it can succeed." ] .+ Shallow
   , external "all-bu"     (allbuR :: RewriteH Core -> RewriteH Core)
       [ "Promote a rewrite to operate over an entire tree in bottom-up order, requiring success at every node." ] .+ Deep
   , external "all-td"     (alltdR :: RewriteH Core -> RewriteH Core)
       [ "Promote a rewrite to operate over an entire tree in top-down order, requiring success at every node." ] .+ Deep
   , external "all-du"     (allduR :: RewriteH Core -> RewriteH Core)
       [ "Apply a rewrite twice, in a top-down and bottom-up way, using one single tree traversal,",
         "succeeding if they all succeed."] .+ Deep
   , external "any-bu"     (anybuR :: RewriteH Core -> RewriteH Core)
       [ "Promote a rewrite to operate over an entire tree in bottom-up order, requiring success for at least one node." ] .+ Deep
   , external "any-td"     (anytdR :: RewriteH Core -> RewriteH Core)
       [ "Promote a rewrite to operate over an entire tree in top-down order, requiring success for at least one node." ] .+ Deep
   , external "any-du"     (anyduR :: RewriteH Core -> RewriteH Core)
       [ "Apply a rewrite twice, in a top-down and bottom-up way, using one single tree traversal,",
         "succeeding if any succeed."] .+ Deep
   , external "one-td"     (onetdR :: RewriteH Core -> RewriteH Core)
       [ "Apply a rewrite to the first node (in a top-down order) for which it can succeed." ] .+ Deep
   , external "one-bu"     (onebuR :: RewriteH Core -> RewriteH Core)
       [ "Apply a rewrite to the first node (in a bottom-up order) for which it can succeed." ] .+ Deep
   , external "prune-td"   (prunetdR :: RewriteH Core -> RewriteH Core)
       [ "Attempt to apply a rewrite in a top-down manner, prunning at successful rewrites." ] .+ Deep
   , external "innermost"  (innermostR :: RewriteH Core -> RewriteH Core)
       [ "A fixed-point traveral, starting with the innermost term." ] .+ Deep .+ Loop
   , external "focus"      (hfocusR :: TranslateH Core LocalPathH -> RewriteH Core -> RewriteH Core)
       [ "Apply a rewrite to a focal point."] .+ Navigation .+ Deep
   , external "focus"      (hfocusT :: TranslateH Core LocalPathH -> TranslateH Core String -> TranslateH Core String)
       [ "Apply a query at a focal point."] .+ Navigation .+ Deep
   , external "focus"      (hfocusR . return :: LocalPathH -> RewriteH Core -> RewriteH Core)
       [ "Apply a rewrite to a focal point."] .+ Navigation .+ Deep
   , external "focus"      (hfocusT . return :: LocalPathH -> TranslateH Core String -> TranslateH Core String)
       [ "Apply a query at a focal point."] .+ Navigation .+ Deep
   , external "when"       ((>>) :: TranslateH Core () -> RewriteH Core -> RewriteH Core)
       [ "Apply a rewrite only if the check succeeds." ] .+ Predicate
   , external "not"        (notM :: TranslateH Core () -> TranslateH Core ())
       [ "Cause a failing check to succeed, a succeeding check to fail." ] .+ Predicate
   , external "invert"     (invertBiT :: BiRewriteH Core -> BiRewriteH Core)
       [ "Reverse a bidirectional rewrite." ]
   , external "forward"    (forwardT :: BiRewriteH Core -> RewriteH Core)
       [ "Apply a bidirectional rewrite forewards." ]
   , external "backward"   (backwardT :: BiRewriteH Core -> RewriteH Core)
       [ "Apply a bidirectional rewrite backwards." ]
   , external "test"       (testQuery :: RewriteH Core -> TranslateH Core String)
       [ "Determine if a rewrite could be successfully applied." ]
   , external "any-call" (anyCallR :: RewriteH Core -> RewriteH Core)
       [ "any-call (.. unfold command ..) applies an unfold command to all applications."
       , "Preference is given to applications with more arguments." ] .+ Deep
   ]

------------------------------------------------------------------------------------

hfocusR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, HasEmptyContext c, MonadCatch m) => Translate c m Core LocalPathH -> Rewrite c m Core -> Rewrite c m Core
hfocusR tp r = do lp <- tp
                  localPathR lp r
{-# INLINE hfocusR #-}

hfocusT :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, HasEmptyContext c, MonadCatch m) => Translate c m Core LocalPathH -> Translate c m Core String -> Translate c m Core String
hfocusT tp t = do lp <- tp
                  localPathT lp t
{-# INLINE hfocusT #-}

------------------------------------------------------------------------------------

-- | Test if a rewrite would succeed, producing a string describing the result.
testQuery :: MonadCatch m => Rewrite c m g -> Translate c m g String
testQuery r = f `liftM` testM r
  where
    f :: Bool -> String
    f True  = "Rewrite would succeed."
    f False = "Rewrite would fail."
{-# INLINE testQuery #-}

------------------------------------------------------------------------------------

-- | Top-down traversal tuned to matching function calls.
anyCallR :: forall c m. (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, HasEmptyContext c, MonadCatch m)
         => Rewrite c m Core -> Rewrite c m Core
anyCallR rr = prefixFailMsg "any-call failed: " $
              readerT $ \ e -> case e of
        ExprCore (App {}) -> childR App_Arg rec >+> (rr <+ childR App_Fun rec)
        ExprCore (Var {}) -> rr
        _                 -> anyR rec
    where rec :: Rewrite c m Core
          rec = anyCallR rr

------------------------------------------------------------------------------------
