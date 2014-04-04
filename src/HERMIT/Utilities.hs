module HERMIT.Utilities
  ( -- * Utilities
    nodups
  , dups
  , dupsBy
  , soleElement
  , equivalentBy
  , equivalent
  , whenJust
  , maybeM
  )
where

------------------------------------------------------------------------------

-- | Determine if a list contains no duplicated elements.
nodups :: Eq a => [a] -> Bool
nodups []     = True
nodups (a:as) = (a `notElem` as) && nodups as

-- | Generalisation of 'dups' to an arbitrary equality predicate.
dupsBy :: (a -> a -> Bool) -> [a] -> [a]
dupsBy _ []     = []
dupsBy p (a:as) = let ds = dupsBy p as
                   in if any (p a) as
                        then a : ds
                        else ds

-- | Discard the last occurrence of each element in the list.  Thus the returned list contains only the duplicated elements.
dups :: Eq a => [a] -> [a]
dups = dupsBy (==)

soleElement :: Monad m => [a] -> m a
soleElement []  = fail "soleElement: list is empty."
soleElement [a] = return a
soleElement _   = fail "soleElement: multiple elements found."

------------------------------------------------------------------------------

-- Drew: surely this exists generally somewhere?
-- for instance:
--      equivalentBy ((==) `on` length) :: [[a]] -> Bool
-- checks if all lists have the same length

-- | A generalisation of 'equivalent' to any equivalence relation.
--   @equivalent = equivalentBy (==)@
equivalentBy :: (a -> a -> Bool) -> [a] -> Bool
equivalentBy _  []     = True
equivalentBy eq (x:xs) = all (eq x) xs

-- | Determine if all elements of a list are equal.
equivalent :: Eq a => [a] -> Bool
equivalent = equivalentBy (==)

------------------------------------------------------------------------------

-- | Perform the monadic action only in the 'Just' case.
whenJust :: Monad m => (a -> m ()) -> Maybe a -> m ()
whenJust f = maybe (return ()) f

-- | Lift a 'Maybe' into an arbitrary monad, using 'return' or 'fail'.
maybeM :: Monad m => String -> Maybe a -> m a
maybeM msg = maybe (fail msg) return

------------------------------------------------------------------------------
