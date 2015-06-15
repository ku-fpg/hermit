{-# LANGUAGE FlexibleContexts, ScopedTypeVariables, LambdaCase #-}

module HERMIT.Dictionary.Kure
    ( -- * KURE Strategies
      externals
    , anyCallR
    , betweenR
    , anyCallR_LCore
    , testQuery
    , hfocusR
    , hfocusT
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
   [ external "id"         (idR :: RewriteH LCore)
       [ "Perform an identity rewrite."] .+ Shallow
   , external "id"         (idR :: RewriteH LCoreTC)
       [ "Perform an identity rewrite."] .+ Shallow
   , external "success"    (successT :: TransformH LCore ())
       [ "An always succeeding translation." ]
   , external "fail"       (fail :: String -> RewriteH LCore)
       [ "A failing rewrite."]
   , external "<+"         ((<+) :: RewriteH LCore -> RewriteH LCore -> RewriteH LCore)
       [ "Perform the first rewrite, and then, if it fails, perform the second rewrite." ]
   , external "<+"         ((<+) :: TransformH LCore () -> TransformH LCore () -> TransformH LCore ())
       [ "Perform the first check, and then, if it fails, perform the second check." ]
   , external ">>>"        ((>>>) :: RewriteH LCore -> RewriteH LCore -> RewriteH LCore)
       [ "Compose rewrites, requiring both to succeed." ]
   , external ">>>"        ((>>>) :: BiRewriteH LCore -> BiRewriteH LCore -> BiRewriteH LCore)
       [ "Compose bidirectional rewrites, requiring both to succeed." ]
   , external ">>>"        ((>>>) :: RewriteH LCoreTC -> RewriteH LCoreTC -> RewriteH LCoreTC)
       [ "Compose rewrites, requiring both to succeed." ]
   , external ">+>"        ((>+>) :: RewriteH LCore -> RewriteH LCore -> RewriteH LCore)
       [ "Compose rewrites, allowing one to fail." ]
   , external "try"        (tryR :: RewriteH LCore -> RewriteH LCore)
       [ "Try a rewrite, and perform the identity if the rewrite fails." ]
   , external "repeat"     (repeatR :: RewriteH LCore -> RewriteH LCore)
       [ "Repeat a rewrite until it would fail." ] .+ Loop
   , external "replicate"  ((\ n -> andR . replicate n)  :: Int -> RewriteH LCore -> RewriteH LCore)
       [ "Repeat a rewrite n times." ]
   , external "all"        (allR :: RewriteH LCore -> RewriteH LCore)
       [ "Apply a rewrite to all children of the node, requiring success at every child." ] .+ Shallow
   , external "any"        (anyR :: RewriteH LCore -> RewriteH LCore)
       [ "Apply a rewrite to all children of the node, requiring success for at least one child." ] .+ Shallow
   , external "one"        (oneR :: RewriteH LCore -> RewriteH LCore)
       [ "Apply a rewrite to the first child of the node for which it can succeed." ] .+ Shallow
   , external "all-bu"     (allbuR :: RewriteH LCore -> RewriteH LCore)
       [ "Promote a rewrite to operate over an entire tree in bottom-up order, requiring success at every node." ] .+ Deep
   , external "all-td"     (alltdR :: RewriteH LCore -> RewriteH LCore)
       [ "Promote a rewrite to operate over an entire tree in top-down order, requiring success at every node." ] .+ Deep
   , external "all-du"     (allduR :: RewriteH LCore -> RewriteH LCore)
       [ "Apply a rewrite twice, in a top-down and bottom-up way, using one single tree traversal,",
         "succeeding if they all succeed."] .+ Deep
   , external "any-bu"     (anybuR :: RewriteH LCore -> RewriteH LCore)
       [ "Promote a rewrite to operate over an entire tree in bottom-up order, requiring success for at least one node." ] .+ Deep
   , external "any-td"     (anytdR :: RewriteH LCore -> RewriteH LCore)
       [ "Promote a rewrite to operate over an entire tree in top-down order, requiring success for at least one node." ] .+ Deep
   , external "any-du"     (anyduR :: RewriteH LCore -> RewriteH LCore)
       [ "Apply a rewrite twice, in a top-down and bottom-up way, using one single tree traversal,",
         "succeeding if any succeed."] .+ Deep
   , external "one-td"     (onetdR :: RewriteH LCore -> RewriteH LCore)
       [ "Apply a rewrite to the first node (in a top-down order) for which it can succeed." ] .+ Deep
   , external "one-bu"     (onebuR :: RewriteH LCore -> RewriteH LCore)
       [ "Apply a rewrite to the first node (in a bottom-up order) for which it can succeed." ] .+ Deep
   , external "prune-td"   (prunetdR :: RewriteH LCore -> RewriteH LCore)
       [ "Attempt to apply a rewrite in a top-down manner, prunning at successful rewrites." ] .+ Deep
   , external "innermost"  (innermostR :: RewriteH LCore -> RewriteH LCore)
       [ "A fixed-point traveral, starting with the innermost term." ] .+ Deep .+ Loop
   , external "focus"      (hfocusR :: TransformH LCoreTC LocalPathH -> RewriteH LCoreTC -> RewriteH LCoreTC)
       [ "Apply a rewrite to a focal point."] .+ Navigation .+ Deep
   , external "focus"      (hfocusT :: TransformH LCoreTC LocalPathH -> TransformH LCoreTC String -> TransformH LCoreTC String)
       [ "Apply a query at a focal point."] .+ Navigation .+ Deep
   , external "focus"      ((\p -> hfocusR (return p)) :: LocalPathH -> RewriteH LCoreTC -> RewriteH LCoreTC)
       [ "Apply a rewrite to a focal point."] .+ Navigation .+ Deep
   , external "focus"      ((\p -> hfocusT (return p)) :: LocalPathH -> TransformH LCoreTC String -> TransformH LCoreTC String)
       [ "Apply a query at a focal point."] .+ Navigation .+ Deep
   , external "focus"      (hfocusR :: TransformH LCore LocalPathH -> RewriteH LCore -> RewriteH LCore)
       [ "Apply a rewrite to a focal point."] .+ Navigation .+ Deep
   , external "focus"      (hfocusT :: TransformH LCore LocalPathH -> TransformH LCore String -> TransformH LCore String)
       [ "Apply a query at a focal point."] .+ Navigation .+ Deep
   , external "focus"      ((\p -> hfocusR (return p)) :: LocalPathH -> RewriteH LCore -> RewriteH LCore)
       [ "Apply a rewrite to a focal point."] .+ Navigation .+ Deep
   , external "focus"      ((\p -> hfocusT (return p)) :: LocalPathH -> TransformH LCore String -> TransformH LCore String)
       [ "Apply a query at a focal point."] .+ Navigation .+ Deep
   , external "when"       ((>>) :: TransformH LCore () -> RewriteH LCore -> RewriteH LCore)
       [ "Apply a rewrite only if the check succeeds." ] .+ Predicate
   , external "not"        (notM :: TransformH LCore () -> TransformH LCore ())
       [ "Cause a failing check to succeed, a succeeding check to fail." ] .+ Predicate
   , external "invert"     (invertBiT :: BiRewriteH LCore -> BiRewriteH LCore)
       [ "Reverse a bidirectional rewrite." ]
   , external "forward"    (forwardT :: BiRewriteH LCore -> RewriteH LCore)
       [ "Apply a bidirectional rewrite forewards." ]
   , external "backward"   (backwardT :: BiRewriteH LCore -> RewriteH LCore)
       [ "Apply a bidirectional rewrite backwards." ]
   , external "test"       (testQuery :: RewriteH LCore -> TransformH LCore String)
       [ "Determine if a rewrite could be successfully applied." ]
   , external "any-call"   (anyCallR_LCore :: RewriteH LCore -> RewriteH LCore)
       [ "any-call (.. unfold command ..) applies an unfold command to all applications."
       , "Preference is given to applications with more arguments." ] .+ Deep
   , external "promote"    (promoteR :: RewriteH LCore -> RewriteH LCoreTC)
       [ "Promote a RewriteCore to a RewriteCoreTC" ]
   , external "extract"    (extractR :: RewriteH LCoreTC -> RewriteH LCore)
       [ "Extract a RewriteCore from a RewriteCoreTC" ]
   , external "extract"    (extractT :: TransformH LCoreTC String -> TransformH LCore String)
       [ "Extract a TransformLCoreString from a TransformLCoreTCString" ]
   , external "between"    (betweenR :: Int -> Int -> RewriteH LCoreTC -> RewriteH LCoreTC)
       [ "between x y rr -> perform rr at least x times and at most y times." ]
   , external "atPath"     (flip hfocusT idR :: TransformH LCore LocalPathH -> TransformH LCore LCore)
       [ "return the expression found at the given path" ]
   , external "atPath"     (flip hfocusT idR :: TransformH LCoreTC LocalPathH -> TransformH LCoreTC LCoreTC)
       [ "return the expression found at the given path" ]
   , external "atPath"     (extractT . flip hfocusT projectT :: TransformH LCoreTC LocalPathH -> TransformH LCore LCore)
       [ "return the expression found at the given path" ]
   ]

------------------------------------------------------------------------------------

hfocusR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, HasEmptyContext c, Walker c u, MonadCatch m)
        => Transform c m u LocalPathH -> Rewrite c m u -> Rewrite c m u
hfocusR tp r = do lp <- tp
                  localPathR lp r
{-# INLINE hfocusR #-}

hfocusT :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, HasEmptyContext c, Walker c u, MonadCatch m)
        => Transform c m u LocalPathH -> Transform c m u b -> Transform c m u b
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
              readerT $ \case
                           ExprCore (App {}) -> childR App_Arg (anyCallR rr)
                                                >+> (rr <+ childR App_Fun (anyCallR rr))
                           ExprCore (Var {}) -> rr
                           _                 -> anyR (anyCallR rr)

-- | Top-down traversal tuned to matching function calls.
anyCallR_LCore :: forall c m. (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, HasEmptyContext c, LemmaContext c, MonadCatch m)
         => Rewrite c m LCore -> Rewrite c m LCore
anyCallR_LCore rr = prefixFailMsg "any-call failed: " $
              readerT $ \case
                           LCore (ExprCore (App {})) ->     childR App_Arg (anyCallR_LCore rr)
                                                        >+> (rr <+ childR App_Fun (anyCallR_LCore rr))
                           LCore (ExprCore (Var {})) -> rr
                           _                         -> anyR (anyCallR_LCore rr)

-- TODO: sort out this duplication

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

------------------------------------------------------------------------------------
