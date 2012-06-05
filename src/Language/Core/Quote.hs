{-# LANGUAGE KindSignatures, GADTs #-}
module Language.Core.Quote where

import GhcPlugins

import Control.Applicative


data Q :: * -> * where
        Q :: (QEnv -> [a]) -> Q a     -- no error msg, yet

data QEnv = QEnv [(Id,Expr Id)] (Expr Id)

instance Functor Q where
  fmap f (Q x) = Q $ \ env -> fmap f (x env)

instance Applicative Q where
  pure x = Q $ \ _ -> pure x
  (Q f) <*> (Q x) = Q $ \ env -> f env <*> x env

instance Alternative Q where
  empty = Q $ \ _ -> []
  (Q x) <|> (Q y) = Q $ \ env -> x env ++ y env


runQ :: Q a -> Expr Id -> Either String a
runQ (Q f) core = case f $ QEnv [] core of
              [a] -> Right a
              []  -> Left "no parse"
              _   -> Left "multiple parses"

infixl 4 <@>

-- match application
(<@>) :: Q (a -> b) -> Q a -> Q b
qab <@> qb = (\ (f,a) -> f a) <$> app qab qb

app :: Q a -> Q b -> Q (a,b)
app (Q qa) (Q qb) = Q $ \ (QEnv env core) -> case core of
        App e1 e2 -> do v1 <- qa $ normalizeQEnv $ QEnv env e1
                        v2 <- qb $ normalizeQEnv $ QEnv env e2
                        return (v1,v2)
        _       -> []

-- I can not remember what this does?
-- Something about jumping over the big lambdas?
normalizeQEnv :: QEnv -> QEnv
normalizeQEnv other = other

integer :: Q Integer
integer = error "integer"

machInt :: Q Integer
machInt = Q $ \ (QEnv _env core) -> case core of
                Lit (MachInt i) -> [i]
                _               -> []

{-
var :: Q String
var = Q $ \ (QEnv env core) -> case core of
                Var str -> [str]
                _       -> []
-}
{-
ident :: TH.Name -> Q ()
ident nm = Q $ \ (QEnv env core) -> case core of
                Var v | nm `cmpName` (idName v) -> [()]
                _       -> []


-- Hacks till we can find the correct way of doing these.
cmpName :: TH.Name -> Name -> Bool
cmpName = undefined
-}

---------------------------------------------------
-- test
{-
data EXP0 = PRINT EXP1
        deriving Show
data EXP1 = VAR String
          | INTEGER Integer
        deriving Show

example0 = var
core0    = Var "print"

core1 = Var "print" `App` Var "x"
exp0 :: Q EXP0
exp0 = PRINT <$ ident "print" <@> exp1

exp1 :: Q EXP1
exp1 = VAR <$> var              <|>
       INTEGER <$> machInt
-}
{-
---------------------------------------------------
-- import

data Expr b
  = Var   Id
  | Lit   Literal
  | App   (Expr b) (Arg b)
  | Lam   b (Expr b)
  | Let   (Bind b) (Expr b)
  | Case  (Expr b) b Type [Alt b]       -- See #case_invariant#
  | Cast  (Expr b) Coercion
  | Tick  (Tickish Id) (Expr b)
  | Type  Type
  | Coercion Coercion

type Arg b = Expr b

type Alt b = (AltCon, [b], Expr b)

data AltCon
  = DataAlt DataCon   --  ^ A plain data constructor: @case e of { Foo x -> ... }@.
                      -- Invariant: the 'DataCon' is always from a @data@ type,
                      -- and never from a @newtype@

  | LitAlt  Literal   -- ^ A literal: @case e of { 1 -> ... }@
                      -- Invariant: always an *unlifted* literal
                      -- See Note [Literal alternatives]

  | DEFAULT           -- ^ Trivial alternative: @case e of { _ -> ... }@

data Bind b = NonRec b (Expr b)
            | Rec [(b, (Expr b))]

---------------------------------------------

data Literal
        = MachChar Char
        | MachInt Integer

data Type = Type_
type Id = String
type Name = String
data Lit = Lit_
data Coercion = Coercion_
data Tickish a = Tickish_
data DataCon = DataCon_

-}
