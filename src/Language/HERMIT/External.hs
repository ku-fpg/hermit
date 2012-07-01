{-# LANGUAGE TypeFamilies, DeriveDataTypeable, FlexibleContexts,
             GADTs, TypeSynonymInstances, FlexibleInstances #-}

module Language.HERMIT.External
       (
       -- * Externals
         External
       , ExternalName
       , ExternalHelp
       , externName
       , externFun
       , externHelp
       , toDictionary
       , toHelp
       , external
       , Extern(..)
       -- * Tags
       , CmdTag(..)
       , TagE
       , Tag((.+),remTag,tagMatch)
       , (.&)
       , (.||)
       , notT
       , externTags
       , dictionaryOfTags
       -- * Boxes
       -- | Boxes are used by the 'Extern' class.
       , TagBox(..)
       , IntBox(..)
       , RewriteCoreBox(..)
       , TranslateCoreStringBox(..)
       , NameBox(..)
       , TranslateCorePathBox(..)
       , StringBox(..)

) where

import Data.Map hiding (map)
import Data.Dynamic
import Data.List

import qualified Language.Haskell.TH as TH

import Language.HERMIT.Kure

-----------------------------------------------------------------

-- | 'External' names are just strings.
type ExternalName = String

-- | Help information for 'External's is stored as a list of strings, designed for multi-line displaying.
type ExternalHelp = [String]

-- Tags --------------------------------------------------------

-- | Requirement: commands cannot have the same name as any 'CmdTag'
--   (or the help function will not find it).
--   These should be /user facing/, because they give the user
--   a way of sub-dividing our confusing array of commands.

data CmdTag = Shell          -- ^ Shell command.
            | Eval           -- ^ The arrow of evaluation (reduces a term).
            | KURE           -- ^ 'Language.KURE' command.
            | Loop           -- ^ Command may operate multiple times.
            | Deep           -- ^ O(n)
            | Shallow        -- ^ O(1)
            | Navigation     -- ^ Uses 'Path' or 'Lens' to focus onto something.
            | Query          -- ^ A question we ask.
            | Predicate      -- ^ Something that passes or fails.
            | Introduce      -- ^ Introduce something, like a new name.
            | Commute        -- ^ It's all about the commute.
            | PreCondition   -- ^ Operation has a precondition.
            | Debug          -- ^ Commands to help debugging.
            | VersionControl -- ^ Version control.
            | Bash           -- ^ Commands that are run by 'Language.HERMIT.Dicitonary.bash'.

            | TODO           -- ^ TODO: check before the release.
            | Unimplemented  -- ^ Something is not finished yet, do not use.
            | Experiment     -- ^ Things we are trying out.


-- Unsure about these
{-
            | Local         -- local thing, O(1)
            | CaseCmd       -- works on case statements
            | Context       -- something that uses the context
            | GHC           -- a tunnel into GHC
            | Lens          -- focuses into a specific node
            | LetCmd        -- works on let statements
            | Meta          -- combines other commands
            | Restful       -- RESTful API commands
            | Slow          -- this command is slow
-}
            -- Other String
            -- etc
    deriving (Eq, Show, Read, Bounded, Enum)

-- | Lists all the tags paired with a short description of what they're about.
dictionaryOfTags :: [(CmdTag,String)]
dictionaryOfTags = notes ++ [ (tag,"(unknown purpose)")
                            | tag <- [minBound..maxBound]
                            , tag `notElem` map fst notes
                            ]
  where notes =
          -- These should give the user a clue about what the sub-commands
          -- might do
          [ (Shell,        "Shell-specific commands")
          , (Eval,         "The arrow of evaluation (reduces a term)")
          , (KURE,         "Commands the directly reflect the KURE DSL")
          , (Loop,        "Command may operate multiple times")
          , (Deep,         "Command may make a deep change, can be O(n)")
          , (Shallow,      "Command operates on local nodes only, O(1)")
          , (Navigation,   "Navigate via focus, or directional command")
          , (Query,        "Questions we ask")
          , (Predicate,    "Something that passes or fails")
          , (Introduce,    "Introduce something, like a new name")
          , (Commute,      "Commute is when you swap nested terms")
          , (PreCondition, "Operation has a (perhaps undocumented) precondition")
          , (Debug,        "Commands specifically to help debugging")
          , (VersionControl,"Version Control for Core Syntax")
          , (Bash,         "Commands that run as part of the bash command.")

          , (TODO,         "TO BE assessed before a release")
          , (Unimplemented,"Something is not finished yet; do not used")
          , (Experiment,   "Things we are trying out")
          ]


-- Unfortunately, record update syntax seems to associate to the right.
-- This guy saves us some parentheses.
infixl 3 .+
infixr 4 .||
infixr 5 .&

-- | A data type of logical operations on tags.
data TagE :: * where
    Tag    :: Tag a => a -> TagE
    NotTag :: TagE -> TagE
    AndTag :: TagE -> TagE -> TagE
    OrTag  :: TagE -> TagE -> TagE

-- | Tags are meta-data that we add to 'External's to make them sortable and searchable.
class Tag a where
    toTagE :: a -> TagE

    -- | Add a 'Tag' to an 'External'.
    (.+) :: External -> a -> External

    -- | Remove a 'Tag' from an 'External'.
    remTag :: a -> External -> External

    -- | Check if an 'External' has the specified 'Tag'.
    tagMatch :: a -> External -> Bool

instance Tag TagE where
    toTagE = id

    e .+ (Tag t) = e .+ t
    e .+ (NotTag t) = remTag t e
    e .+ (AndTag t1 t2) = e .+ t1 .+ t2
    e .+ (OrTag t1 t2) = e .+ t1 .+ t2 -- not sure what else to do

    remTag (Tag t) e = remTag t e
    remTag (NotTag t) e = e .+ t
    remTag (AndTag t1 t2) e = remTag t1 (remTag t2 e)
    remTag (OrTag t1 t2) e = remTag t1 (remTag t2 e) -- again

    tagMatch (Tag t)        e = tagMatch t e
    tagMatch (NotTag t)     e = not (tagMatch t e)
    tagMatch (AndTag t1 t2) e = tagMatch t1 e && tagMatch t2 e
    tagMatch (OrTag  t1 t2) e = tagMatch t1 e || tagMatch t2 e

instance Tag CmdTag where
    toTagE = Tag
    ex@(External {externTags = ts}) .+ t = ex {externTags = t:ts}
    remTag t ex@(External {externTags = ts}) = ex { externTags = [ t' | t' <- ts, t' /= t ] }
    tagMatch t (External {externTags = ts}) = t `elem` ts

-- | An \"and\" on 'Tag's.
(.&) :: (Tag a, Tag b) => a -> b -> TagE
t1 .& t2 = AndTag (toTagE t1) (toTagE t2)

-- | An \"or\" on 'Tag's.
(.||) :: (Tag a, Tag b) => a -> b -> TagE
t1 .|| t2 = OrTag (toTagE t1) (toTagE t2)

-- how to make a unary operator?
-- | A \"not\" on 'Tag's.
notT :: Tag a => a -> TagE
notT = NotTag . toTagE

-----------------------------------------------------------------

-- | An 'External' is a 'Dynamic' value with some associated meta-data (name, help string and tags).
data External = External
        { externName :: ExternalName        -- ^ Get the name of an 'External'.
        , externFun  :: Dynamic             -- ^ Get the 'Dynamic' value stored in an 'External'.
        , externHelp :: ExternalHelp        -- ^ Get the list of help 'String's for an 'External'.
        , externTags :: [CmdTag]            -- ^ List all the 'CmdTag's associated with an 'External'
        }

-- | The primitive way to build an 'External'.
external :: Extern a => ExternalName -> a -> ExternalHelp -> External
external nm fn help = External
        { externName = nm
        , externFun  = toDyn (box fn)
        , externHelp = map ("  " ++) help
        , externTags = []
        }

-- | Build a 'Data.Map' from names to 'Dynamic' values.
toDictionary :: [External] -> Map ExternalName [Dynamic]
toDictionary
        -- TODO: check names are uniquely-prefixed
              = fromListWith (++) . map toD
  where
         toD :: External -> (ExternalName,[Dynamic])
         toD e = (externName e,[externFun e])

-- | Build a 'Data.Map' from names to help information.
toHelp :: [External] -> Map ExternalName ExternalHelp
toHelp = fromListWith (++) . map toH
  where
         toH :: External -> (ExternalName,ExternalHelp)
         toH e = (externName e, spaceout (externName e ++ " :: " ++ fixup (show (dynTypeRep (externFun e))))
                                         (show (externTags e)) : externHelp e)

         spaceout xs ys = xs ++ replicate (width - (length xs + length ys)) ' ' ++ ys

         width = 78

         fixup :: String -> String
         fixup xs | "Box" `isPrefixOf` xs = fixup (drop 3 xs)
         fixup (x:xs)                     = x : fixup xs
         fixup []                         = []


-----------------------------------------------------------------

-- | The class of things that can be made into 'External's.
--   To be an 'Extern' there must exist an isomorphic 'Box' type that is an instance of 'Typeable'.
class Typeable (Box a) => Extern a where

    -- | An isomorphic wrapper.
    type Box a

    -- | Wrap a value in a 'Box'.
    box :: a -> Box a

    -- | Unwrap a value from a 'Box'.
    unbox :: Box a -> a

instance (Extern a, Extern b) => Extern (a -> b) where
    type Box (a -> b) = Box a -> Box b
    box f = box . f . unbox
    unbox f = unbox . f . box

data TagBox = TagBox TagE deriving Typeable

instance Extern TagE where
    type Box TagE = TagBox
    box = TagBox
    unbox (TagBox t) = t

data IntBox = IntBox Int deriving Typeable

instance Extern Int where
    type Box Int = IntBox
    box = IntBox
    unbox (IntBox i) = i

data RewriteCoreBox = RewriteCoreBox (RewriteH Core) deriving Typeable

instance Extern (RewriteH Core) where
    type Box (RewriteH Core) = RewriteCoreBox
    box = RewriteCoreBox
    unbox (RewriteCoreBox i) = i

data TranslateCoreStringBox = TranslateCoreStringBox (TranslateH Core String) deriving Typeable

instance Extern (TranslateH Core String) where
    type Box (TranslateH Core String) = TranslateCoreStringBox
    box = TranslateCoreStringBox
    unbox (TranslateCoreStringBox i) = i

data NameBox = NameBox (TH.Name) deriving Typeable

instance Extern TH.Name where
    type Box TH.Name = NameBox
    box = NameBox
    unbox (NameBox i) = i

data TranslateCorePathBox = TranslateCorePathBox (TranslateH Core Path) deriving Typeable

instance Extern (TranslateH Core Path) where
    type Box (TranslateH Core Path) = TranslateCorePathBox
    box = TranslateCorePathBox
    unbox (TranslateCorePathBox i) = i


data StringBox = StringBox String deriving Typeable

instance Extern String where
    type Box String = StringBox
    box = StringBox
    unbox (StringBox i) = i

-----------------------------------------------------------------
