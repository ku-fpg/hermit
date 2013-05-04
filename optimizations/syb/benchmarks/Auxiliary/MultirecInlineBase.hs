{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE Rank2Types            #-}

module Auxiliary.MultirecInlineBase where

import Control.Applicative

-- * Structure types

infixr 5 :+:
infix  6 :>:
infixr 7 :*:

-- | Represents recursive positions. The first argument indicates
-- which type to recurse on.
data I xi      (r :: * -> *) ix = I {unI :: !(r xi)}

-- | Represents constant types that do not belong to the family.
data K a       (r :: * -> *) ix = K {unK :: !a}

-- | Represents constructors without fields.
data U         (r :: * -> *) ix = U

-- | Represents sums (choices between constructors).
data (f :+: g) (r :: * -> *) ix = L (f r ix) | R (g r ix)

-- | Represents products (sequences of fields of a constructor).
data (f :*: g) (r :: * -> *) ix = f r ix :*: g r ix

-- | Is used to indicate the type that a
-- particular constructor injects to.
data f :>: ix :: (* -> *) -> * -> * where
  Tag :: !(f r ix) -> (f :>: ix) r ix

-- | Destructor for '(:>:)'.
unTag :: (f :>: ix) r ix -> f r ix
unTag (Tag x) = x

-- | Represents constructors.
data C c f     (r :: * -> *) ix where
  C :: !(f r ix) -> C c f r ix

-- | Destructor for 'C'.
unC :: C c f r ix -> f r ix
unC (C x) = x

-- ** Unlifted variants

-- | Unlifted version of 'I'.
data I0 a   = I0 { unI0 :: !a }

-- | Unlifted version of 'K'.
data K0 a b = K0 { unK0 :: !a }

instance Functor I0 where
  fmap f = I0 . f . unI0

instance Applicative I0 where
  pure              = I0
  (I0 f) <*> (I0 x) = I0 (f x)

instance Functor (K0 a) where
  fmap f = K0 . unK0

-- * Indexed families

-- | Type family describing the pattern functor of a family.
type family PF phi :: (* -> *) -> * -> *

-- | Class for the members of a family.
class El phi ix where
  proof :: phi ix

-- | For backwards-compatibility: a synonym for 'proof'.
index :: El phi ix => phi ix
index = proof

-- | Class that contains the shallow conversion functions for a family.
class Fam phi where
  from :: phi ix -> ix -> PF phi I0 ix
  to   :: phi ix -> PF phi I0 ix -> ix

-- | Semi-decidable equality for types of a family.
class EqS phi where
  eqS :: phi ix -> phi ix' -> Maybe (ix :=: ix')


-- Metadata stuff

-- | Class for datatypes that represent data constructors.
-- For non-symbolic constructors, only 'conName' has to be defined.
-- The weird argument is supposed to be instantiated with 'C' from
-- base, hence the complex kind.
class Constructor c where
  conName   :: t c (f :: (* -> *) -> * -> *) (r :: * -> *) ix -> String
  conFixity :: t c (f :: (* -> *) -> * -> *) (r :: * -> *) ix -> Fixity
  conFixity = const Prefix

-- | Datatype to represent the fixity of a constructor. An infix declaration
-- directly corresponds to an application of 'Infix'.
data Fixity = Prefix | Infix Associativity Int
  deriving (Eq, Show, Ord, Read)

data Associativity = LeftAssociative | RightAssociative | NotAssociative
  deriving (Eq, Show, Ord, Read)

-- TEq stuff

infix 4 :=:

data (:=:) :: * -> * -> * where
  Refl :: a :=: a

cast :: a :=: b -> a -> b
cast Refl x = x
