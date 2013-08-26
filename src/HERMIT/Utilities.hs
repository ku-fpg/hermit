module HERMIT.Utilities
  ( -- * Utilities
    nodups
  , whenJust
  )
where

------------------------------------------------------------------------------

-- | Determine if a list contains no duplicated elements.
nodups :: Eq a => [a] -> Bool
nodups []     = True
nodups (a:as) = (a `notElem` as) && nodups as

-- | Perform the monadic action only in the 'Just' case.
whenJust :: Monad m => (a -> m ()) -> Maybe a -> m ()
whenJust f = maybe (return ()) f

------------------------------------------------------------------------------
