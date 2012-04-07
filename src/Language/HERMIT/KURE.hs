{-# LANGUAGE TypeFamilies, FlexibleInstances, ScopedTypeVariables #-}

module Language.HERMIT.KURE where

import Data.Monoid
import Control.Arrow
import qualified Control.Category as Cat
import Control.Monad

import Language.HERMIT.Types
import Language.HERMIT.HermitMonad
import Language.HERMIT.HermitEnv

--infixl 3 <+, >->, .+, !->
--infixr 3 ?

-- Note: We use < for catching fail, . for catching id.

--------------------------------------------------------------------------------
-- The Translate combinators.

-- | like a catch, '<+' does the first translate, and if it fails, then does the second translate.
--(<+) :: Translate a b -> Translate a b -> Translate a b
--(<+) rr1 rr2 = translate $ \ (Context c e) -> apply rr1 (Context c e) `catchH` (\ _ -> apply rr2 (Context c e))

infixl 3 >->

-- Should this be Rewrite b -> Translate b c -> Translate b c
(>->) :: Translate b b -> Translate b c -> Translate b c
(>->) rr1 rr2 = translate $ \ (Context c e0)  -> do
        e1 <- apply rr1 (Context c e0)
        e2 <- apply rr2 (Context c e1)
        return $ e2


-- | failing translation.
failT :: String -> Translate a b
failT msg = translate $ \ _ -> fail msg


-- | look at the argument for the translation before choosing which translation to perform.
readerT :: (a -> Translate a b) -> Translate a b
readerT fn = translate $ \ (Context c expA) -> apply (fn expA) (Context c expA)


-- | lift a function into a Translate
pureT :: (a -> b) -> Translate a b
pureT f = arr (\ (Context _ a) -> f a)



-- | 'constT' always translates into an unfailable 'Translate' that returns the first argument.
constT :: b -> Translate a b
constT = pureT . const


-- | 'concatT' turns a list of 'Translate's that return a common 'Monoid'al result
-- into a single 'Translate' that performs them all in sequence and combines their
-- results with 'mconcat'
concatT :: (Monoid r) => [Translate a r] -> Translate a r
concatT ts = translate $ \ (Context c e) -> do
	rs <- sequence [ apply t (Context c e) | t <- ts ]
	return (mconcat rs)

-- | 'emptyT' is an unfailing 'Translate' that always returns 'mempty'
emptyT :: (Monoid r) => Translate a r
emptyT = constT mempty

--------------------------------------------------------------------------------
{-
-- The 'Rewrite' combinators.
-- | if the first rewrite is an identity, then do the second rewrite.
(.+) :: (Term a) => Rewrite a -> Rewrite a -> Rewrite a
(.+) r0 r1 = rewrite $ \ e0 -> do
		e1 <- apply r0 e0
		isId <- e0 .==. e1
		if isId then apply r1 e1
			    else return e1

-- | if the first rewrite was /not/ an identity, then also do the second rewrite.
(!->) :: (Term a) => Rewrite a -> Rewrite a -> Rewrite a
(!->) r0 r1 = rewrite $ \ e0 -> do
		e1 <- apply r0 e0
		isId <- e0 .==. e1
		if isId then return e1
			    else apply r1 e1

-- | Term equality
(.==.) :: (TranslateMonad m, Term e) => e -> e -> m Bool
(.==.) = apply . equals
-}
-- | catch a failing 'Rewrite', making it into an identity.
tryR :: Rewrite a -> Rewrite a
tryR s = s <+ idR

{-
-- | if this is an identity rewrite, make it fail. To succeed, something must have changed.
changedR :: (Term a) => Rewrite a -> Rewrite a
changedR rr = rr .+ failR "unchanged"
-}

-- | repeat a rewrite until it fails, then return the result before the failure.
repeatR :: Rewrite a -> Rewrite a
repeatR s = tryR (s >-> repeatR s)

-- | look at the argument to a rewrite, and choose to be either a failure of trivial success.
acceptR :: (a -> Bool) -> Rewrite a
acceptR fn = translate $ \ (Context c expA) -> if fn expA
		    then return expA
	            else fail "accept failed"

-- | identity rewrite.
-- Moved int Types
--idR :: Rewrite exp
--idR = rewrite $ \ (Context _ e) -> return e

-- | failing rewrite.
failR :: String -> Rewrite a
failR = failT

--------------------------------------------------------------------------------
-- Prelude structures

tuple2R :: Rewrite a -> Rewrite b -> Rewrite (a,b)
tuple2R rra rrb = rewrite $ \ (Context c (a,b)) -> liftM2 (,) (apply rra (Context c a)) (apply rrb (Context c b))

listR :: Rewrite a -> Rewrite [a]
listR rr = rewrite $ \ (Context c es) -> mapM (apply rr . Context c) es

maybeR :: Rewrite a -> Rewrite (Maybe a)
maybeR rr = rewrite $ \ (Context c e) -> case e of
		Just e'  -> liftM Just (apply rr (Context c e'))
		Nothing  -> return $ Nothing

tuple2U :: (Monoid r) => Translate a r -> Translate b r -> Translate (a,b) r
tuple2U rra rrb = translate $ \ (Context c (a,b)) -> liftM2 mappend (apply rra (Context c a)) (apply rrb (Context c b))

listU :: (Monoid r) => Translate a r -> Translate [a] r
listU rr = translate $ \ (Context c es) -> liftM mconcat (mapM (apply rr . Context c) es)

maybeU :: ( Monoid r) => Translate a r -> Translate (Maybe a) r
maybeU rr = translate $ \ (Context c e) -> case e of
		Just e'  -> apply rr (Context c e')
		Nothing  -> return $ mempty

--------------------------------------------------------------------------------
-- | Guarded translate or monadic action.
(?) ::  Bool -> Translate a b -> Translate a b
(?) False _rr = failT "(False ?)"
(?) True   rr = rr

-------------------------------------------------------------------------------

-- | apply a rewrite in a top down manner.
topdownR :: ( e ~ Generic e, Term e) => Rewrite (Generic e) -> Rewrite (Generic e)
topdownR  s = s >-> allR (topdownR s)

-- | apply a rewrite in a bottom up manner.
bottomupR :: ( e ~ Generic e, Term e) => Rewrite (Generic e) -> Rewrite (Generic e)
bottomupR s = allR (bottomupR s) >-> s

-- | apply a rewrite in a top down manner, prunning at successful rewrites.
alltdR :: ( e ~ Generic e, Term e) => Rewrite (Generic e) -> Rewrite (Generic e)
alltdR    s = s <+ allR (alltdR s)

-- | apply a rewrite twice, in a topdown and bottom up way, using one single tree traversal.
downupR :: ( e ~ Generic e, Term e) => Rewrite (Generic e) -> Rewrite (Generic e)
downupR   s = s >-> allR (downupR s) >-> s

-- | a fixed point traveral, starting with the innermost term.
innermostR :: ( e ~ Generic e, Term e) => Rewrite (Generic e) -> Rewrite (Generic e)
innermostR s = bottomupR (tryR (s >-> innermostR s))

-- -- | repeatedly apply 'downupR s' until no further changes can be made
--repeatedR :: ( e ~ Generic e, Term e) => Rewrite (Generic e) -> Rewrite (Generic e)
--repeatedR s = downupR s !-> repeatedR s

-- fold a tree using a single translation for each node.
foldU :: ( e ~ Generic e, Term e, Monoid r) => Translate (Generic e) r -> Translate (Generic e) r
foldU s = concatT [ s, crushU (foldU s) ]
---------------------------------------------------------------------

-- | pathT finds the current path.
pathT :: Translate a Path
pathT = translate $ \ (Context c _) -> return (hermitBindingPath c)

---------------------------------------------------------------------
-- Path stuff

pathFinder :: forall e . (Term e, e ~ Generic e) => [Int] -> Rewrite (Generic e) -> Rewrite (Generic e)
pathFinder []     rr = rr
pathFinder (p:ps) rr = allR child
   where
        child :: Rewrite (Generic e)
        child =  pathT >>= \ (Path (t:_)) ->
                        if p == t then pathFinder ps rr
                                  else idR

