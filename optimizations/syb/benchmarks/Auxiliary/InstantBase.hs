{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE TypeFamilies             #-}

module Auxiliary.InstantBase (
      U(..), (:+:)(..), (:*:)(..), C(..), Var(..), Rec(..)
    , Constructor(..), Fixity(..), Associativity(..)
    , Representable(..)
  ) where

infixr 5 :+:
infixr 6 :*:

data U        = U              deriving (Show, Read)
data a :+: b  = L a | R b      deriving (Show, Read)
data a :*: b  = a :*: b        deriving (Show, Read)
newtype C c a = C a            deriving (Show, Read)
newtype Var a = Var a          deriving (Show, Read)
newtype Rec a = Rec a          deriving (Show, Read)

-- | Class for datatypes that represent data constructors.
-- For non-symbolic constructors, only 'conName' has to be defined.
class Constructor c where
  conName   :: t c a -> String
  conFixity :: t c a -> Fixity
  conFixity = const Prefix
  conIsRecord :: t c a -> Bool
  conIsRecord = const False

-- | Datatype to represent the fixity of a constructor. An infix declaration
-- directly corresponds to an application of 'Infix'.
data Fixity = Prefix | Infix Associativity Int
  deriving (Eq, Show, Ord, Read)

-- | Datatype to represent the associativy of a constructor.
data Associativity = LeftAssociative | RightAssociative | NotAssociative
  deriving (Eq, Show, Ord, Read)


class Representable a where
  type Rep a
  to   :: Rep a -> a
  from :: a -> Rep a
  