{-# LANGUAGE FlexibleContexts, ScopedTypeVariables #-}

module HERMIT.Dictionary.Kure
    ( -- * KURE Strategies
      externals
    , anyCallR
    , betweenR
    ) where

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
   , external "id"         (idR :: RewriteH QC)
       [ "Perform an identity rewrite."] .+ Shallow
   , external "success"    (successT :: TransformH Core ())
       [ "An always succeeding translation." ]
   , external "fail"       (fail :: String -> RewriteH Core)
       [ "A failing rewrite."]
   , external "<+"         ((<+) :: RewriteH Core -> RewriteH Core -> RewriteH Core)
       [ "Perform the first rewrite, and then, if it fails, perform the second rewrite." ]
   , external "<+"         ((<+) :: TransformH Core () -> TransformH Core () -> TransformH Core ())
       [ "Perform the first check, and then, if it fails, perform the second check." ]
   , external ">>>"        ((>>>) :: RewriteH Core -> RewriteH Core -> RewriteH Core)
       [ "Compose rewrites, requiring both to succeed." ]
   , external ">>>"        ((>>>) :: BiRewriteH Core -> BiRewriteH Core -> BiRewriteH Core)
       [ "Compose bidirectional rewrites, requiring both to succeed." ]
   , external ">>>"        ((>>>) :: RewriteH QC -> RewriteH QC -> RewriteH QC)
       [ "Compose rewrites, requiring both to succeed." ]
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
   , external "any-td"     (anytdR :: RewriteH QC -> RewriteH QC)
       [ "Promote a rewrite to operate over an entire tree in top-down order, requiring success for at least one node." ] .+ Deep
   , external "any-du"     (anyduR :: RewriteH Core -> RewriteH Core)
       [ "Apply a rewrite twice, in a top-down and bottom-up way, using one single tree traversal,",
         "succeeding if any succeed."] .+ Deep
   , external "one-td"     (onetdR :: RewriteH Core -> RewriteH Core)
       [ "Apply a rewrite to the first node (in a top-down order) for which it can succeed." ] .+ Deep
   , external "one-td"     (onetdR :: RewriteH QC -> RewriteH QC)
       [ "Apply a rewrite to the first node (in a top-down order) for which it can succeed." ] .+ Deep
   , external "one-bu"     (onebuR :: RewriteH Core -> RewriteH Core)
       [ "Apply a rewrite to the first node (in a bottom-up order) for which it can succeed." ] .+ Deep
   , external "prune-td"   (prunetdR :: RewriteH Core -> RewriteH Core)
       [ "Attempt to apply a rewrite in a top-down manner, prunning at successful rewrites." ] .+ Deep
   , external "innermost"  (innermostR :: RewriteH Core -> RewriteH Core)
       [ "A fixed-point traveral, starting with the innermost term." ] .+ Deep .+ Loop
   , external "focus"      (hfocusR :: TransformH QC LocalPathH -> RewriteH QC -> RewriteH QC)
       [ "Apply a rewrite to a focal point."] .+ Navigation .+ Deep
   , external "focus"      (hfocusT :: TransformH QC LocalPathH -> TransformH QC String -> TransformH QC String)
       [ "Apply a query at a focal point."] .+ Navigation .+ Deep
   , external "focus"      ((\t -> hfocusR t . promoteCoreTCR) :: TransformH QC LocalPathH -> RewriteH CoreTC -> RewriteH QC)
       [ "Apply a rewrite to a focal point."] .+ Navigation .+ Deep
   , external "focus"      ((\t -> hfocusT t . promoteCoreTCT) :: TransformH QC LocalPathH -> TransformH CoreTC String -> TransformH QC String)
       [ "Apply a query at a focal point."] .+ Navigation .+ Deep
   , external "focus"      ((\t -> extractR . hfocusR (promoteCoreTCT t) . promoteCoreTCR) :: TransformH CoreTC LocalPathH -> RewriteH CoreTC -> RewriteH CoreTC)
       [ "Apply a rewrite to a focal point."] .+ Navigation .+ Deep
   , external "focus"      ((\t -> extractT . hfocusT (promoteCoreTCT t) . promoteCoreTCT) :: TransformH CoreTC LocalPathH -> TransformH CoreTC String -> TransformH CoreTC String)
       [ "Apply a query at a focal point."] .+ Navigation .+ Deep
   , external "focus"      ((\p -> extractR . hfocusR (return p) . promoteCoreTCR) :: LocalPathH -> RewriteH CoreTC -> RewriteH CoreTC)
       [ "Apply a rewrite to a focal point."] .+ Navigation .+ Deep
   , external "focus"      ((\p -> extractT . hfocusT (return p) . promoteCoreTCT) :: LocalPathH -> TransformH CoreTC String -> TransformH CoreTC String)
       [ "Apply a query at a focal point."] .+ Navigation .+ Deep
   , external "focus"      ((\t -> extractR . hfocusR (promoteCoreTCT t) . promoteCoreR) :: TransformH CoreTC LocalPathH -> RewriteH Core -> RewriteH Core)
       [ "Apply a rewrite to a focal point."] .+ Navigation .+ Deep
   , external "focus"      ((\t -> extractT . hfocusT (promoteCoreTCT t) . promoteCoreT) :: TransformH CoreTC LocalPathH -> TransformH Core String -> TransformH Core String)
       [ "Apply a query at a focal point."] .+ Navigation .+ Deep
   , external "focus"      ((\p -> extractR . hfocusR (return p) . promoteR) :: LocalPathH -> RewriteH Core -> RewriteH Core)
       [ "Apply a rewrite to a focal point."] .+ Navigation .+ Deep
   , external "focus"      ((\p -> extractT . hfocusT (return p) . promoteT) :: LocalPathH -> TransformH Core String -> TransformH Core String)
       [ "Apply a query at a focal point."] .+ Navigation .+ Deep
   , external "when"       ((>>) :: TransformH Core () -> RewriteH Core -> RewriteH Core)
       [ "Apply a rewrite only if the check succeeds." ] .+ Predicate
   , external "not"        (notM :: TransformH Core () -> TransformH Core ())
       [ "Cause a failing check to succeed, a succeeding check to fail." ] .+ Predicate
   , external "invert"     (invertBiT :: BiRewriteH Core -> BiRewriteH Core)
       [ "Reverse a bidirectional rewrite." ]
   , external "forward"    (forwardT :: BiRewriteH Core -> RewriteH Core)
       [ "Apply a bidirectional rewrite forewards." ]
   , external "backward"   (backwardT :: BiRewriteH Core -> RewriteH Core)
       [ "Apply a bidirectional rewrite backwards." ]
   , external "test"       (testQuery :: RewriteH Core -> TransformH Core String)
       [ "Determine if a rewrite could be successfully applied." ]
   , external "any-call"   (anyCallR :: RewriteH Core -> RewriteH Core)
       [ "any-call (.. unfold command ..) applies an unfold command to all applications."
       , "Preference is given to applications with more arguments." ] .+ Deep
   , external "promote"    (promoteR :: RewriteH Core -> RewriteH CoreTC)
       [ "Promote a RewriteCore to a RewriteCoreTC" ]
   , external "promote"    (promoteR :: RewriteH CoreTC -> RewriteH QC)
       [ "Promote a RewriteCoreTC to a RewriteQC" ]
   , external "promote"    (promoteR :: RewriteH Core -> RewriteH QC)
       [ "Promote a RewriteCore to a RewriteQC" ]
   , external "extract"    (extractR :: RewriteH CoreTC -> RewriteH Core)
       [ "Extract a RewriteCore from a RewriteCoreTC" ]
   , external "between"    (betweenR :: Int -> Int -> RewriteH CoreTC -> RewriteH CoreTC)
       [ "between x y rr -> perform rr at least x times and at most y times." ]
   , external "atPath"     (flip hfocusT idR :: TransformH QC LocalPathH -> TransformH QC QC)
       [ "return the expression found at the given path" ]
   ]

------------------------------------------------------------------------------------

hfocusR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, HasEmptyContext c, MonadCatch m)
        => Transform c m QC LocalPathH -> Rewrite c m QC -> Rewrite c m QC
hfocusR tp r = do lp <- tp
                  localPathR lp r
{-# INLINE hfocusR #-}

hfocusT :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, HasEmptyContext c, MonadCatch m)
        => Transform c m QC LocalPathH -> Transform c m QC b -> Transform c m QC b
hfocusT tp t = do lp <- tp
                  localPathT lp t
{-# INLINE hfocusT #-}

------------------------------------------------------------------------------------

-- | Test if a rewrite would succeed, producing a string describing the result.
testQuery :: MonadCatch m => Rewrite c m g -> Transform c m g String
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

-- | betweenR x y rr -> perform rr at least x times and at most y times.
betweenR :: MonadCatch m => Int -> Int -> Rewrite c m a -> Rewrite c m a
betweenR l h rr | l < 0 = fail "betweenR: lower limit below zero"
                | h < l = fail "betweenR: upper limit less than lower limit"
                | otherwise = go 0
    where -- 'c' is number of times rr has run already
          go c | c >= h = idR               -- done
               | c < l  = rr >>> go (c+1)   -- haven't hit lower bound yet
               | otherwise = tryR (rr >>> go (c+1))  -- met lower bound
