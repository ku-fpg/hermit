module HERMIT.Utilities
  ( -- * Utilities
    nodups
  , equivalentBy
  , equivalent
  , whenJust
  )
where

------------------------------------------------------------------------------

-- | Determine if a list contains no duplicated elements.
nodups :: Eq a => [a] -> Bool
nodups []     = True
nodups (a:as) = (a `notElem` as) && nodups as

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

------------------------------------------------------------------------------
