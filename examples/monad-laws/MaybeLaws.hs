module MaybeLaws where

{-# RULES "left-unit"  forall x f.  retur x `bind` f  =  f x  #-}

{-# RULES "right-unit"  forall m.   m `bind` retur  =  m  #-}

bind :: Maybe a -> (a -> Maybe b) -> Maybe b
bind Nothing  k = Nothing
bind (Just a) k = k a

retur :: a -> Maybe a
retur = Just
