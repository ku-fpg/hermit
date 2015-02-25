{-# LANGUAGE GADTs, TypeFamilies, FlexibleContexts, FlexibleInstances, DeriveDataTypeable #-}

module HERMIT.External
    ( -- * Externals
      External
    , ExternalName
    , ExternalHelp
    , externName
    , externDyn
    , externHelp
    , externTypeString
    , externTypeArgResString
    , splitFunTyArgs
    , toHelp
    , external
    , Extern(..)
    , matchingExternals
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
    , BiRewriteCoreBox(..)
    , CoreString(..)
    , CrumbBox(..)
    , IntBox(..)
    , IntListBox(..)
    , PathBox(..)
    , RewriteCoreBox(..)
    , RewriteCoreListBox(..)
    , RewriteCoreTCBox(..)
    , RewriteQCBox(..)
    , StringBox(..)
    , StringListBox(..)
    , TagBox(..)
    , TransformCoreCheckBox(..)
    , TransformCorePathBox(..)
    , TransformCoreStringBox(..)
    , TransformCoreTCCheckBox(..)
    , TransformCoreTCPathBox(..)
    , TransformCoreTCStringBox(..)
    , TransformQCStringBox(..)
    , TransformQCUnitBox(..)
    ) where

import Data.Map hiding (map)
import Data.Dynamic
import Data.List
import Data.Typeable.Internal (TypeRep(..), funTc)

import HERMIT.Core
import HERMIT.Context (LocalPathH)
import HERMIT.Kure
import HERMIT.Lemma

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
data CmdTag = Shell          -- ^ Shell-specific command.
            | Eval           -- ^ The arrow of evaluation (reduces a term).
            | KURE           -- ^ 'Language.KURE' command.
            | Loop           -- ^ Command may operate multiple times.
            | Deep           -- ^ Command may make a deep change, can be O(n).
            | Shallow        -- ^ Command operates on local nodes only, O(1).
            | Navigation     -- ^ Uses 'Path' or 'Lens' to focus onto something.
            | Query          -- ^ Extract information from an expression.
            | Predicate      -- ^ Something that passes or fails.
            | Introduce      -- ^ Introduce something, like a new name.
            | Commute        -- ^ Commute is when you swap nested terms.
            | PreCondition   -- ^ Operation has a (perhaps undocumented) precondition.
            | Strictness     -- ^ Alters the strictness of the expression.
            | Debug          -- ^ Commands specifically to help debugging.
            | VersionControl -- ^ Version control for Core syntax.
            | Context        -- ^ A command that uses its context, such as inlining.
            | Unsafe         -- ^ Commands that are not type safe (may cause Core Lint to fail),
                             --   or may otherwise change the semantics of the program.
            | Proof          -- ^ Commands related to proving lemmas.

            | TODO           -- ^ An incomplete or potentially buggy command.
            | Experiment     -- ^ Things we are trying out.
            | Deprecated     -- ^ A command that will be removed in a future release;
                             --   it has probably been renamed or subsumed by another command.
    deriving (Eq, Show, Read, Bounded, Enum)

-- | Lists all the tags paired with a short description of what they're about.
dictionaryOfTags :: [(CmdTag,String)]
dictionaryOfTags = notes ++ [ (tag,"(unknown purpose)")
                            | tag <- [minBound..maxBound]
                            , tag `notElem` map fst notes
                            ]
  where notes =
          -- These should give the user a clue about what the sub-commands might do
          [ (Shell,          "Shell-specific command.")
          , (Eval,           "The arrow of evaluation (reduces a term).")
          , (KURE,           "Direct reflection of a combinator from the KURE DSL.")
          , (Loop,           "Command may operate multiple times.")
          , (Deep,           "Command may make a deep change, can be O(n).")
          , (Shallow,        "Command operates on local nodes only, O(1).")
          , (Navigation,     "Navigate via focus, or directional command.")
          , (Query,          "Extract information from an expression.")
          , (Predicate,      "Something that passes or fails.")
          , (Introduce,      "Introduce something, like a new name.")
          , (Commute,        "Commute is when you swap nested terms.")
          , (PreCondition,   "Operation has a (perhaps undocumented) precondition.")
          , (Strictness,     "Alters the strictness of an expression.")
          , (Debug,          "A command specifically to help debugging.")
          , (VersionControl, "Version control for Core syntax.")
          , (Context,        "A command that uses its context, such as inlining.")
          , (Unsafe,         "Commands that are not type safe (may cause Core Lint to fail), or may otherwise change the semantics of the program.")
          , (Proof,          "Commands related to proving lemmas.")
          , (TODO,           "An incomplete or potentially buggy command.")
          , (Experiment,     "Things we are trying out, use at your own risk.")
          , (Deprecated,     "A command that will be removed in a future release; it has probably been renamed or subsumed by another command.")
          ]

-- Unfortunately, record update syntax seems to associate to the right.
-- These operators save us some parentheses.
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
        , externDyn  :: Dynamic             -- ^ Get the 'Dynamic' value stored in an 'External'.
        , externHelp :: ExternalHelp        -- ^ Get the list of help 'String's for an 'External'.
        , externTags :: [CmdTag]            -- ^ List all the 'CmdTag's associated with an 'External'
        }

-- | The primitive way to build an 'External'.
external :: Extern a => ExternalName -> a -> ExternalHelp -> External
external nm fn help = External
        { externName = nm
        , externDyn  = toDyn (box fn)
        , externHelp = map ("  " ++) help
        , externTags = []
        }

-- | Get all the 'External's which match a given tag predicate
-- and box a Transform of the appropriate type.
matchingExternals :: (Extern tr, Tag t) => t -> [External] -> [(External, tr)]
matchingExternals tag exts = [ (e,tr) | e <- exts, tagMatch tag e
                                      , Just tr <- [fmap unbox $ fromDynamic $ externDyn e] ]

-- | Build a 'Data.Map' from names to help information.
toHelp :: [External] -> Map ExternalName ExternalHelp
toHelp = fromListWith (++) . map toH
  where
         toH :: External -> (ExternalName,ExternalHelp)
         toH e = (externName e, spaceout (externName e ++ " :: " ++ externTypeString e)
                                         (show (externTags e)) : externHelp e)

         spaceout xs ys = xs ++ replicate (width - (length xs + length ys)) ' ' ++ ys

         width = 78

-- | Get a string representation of the (monomorphic) type of an 'External'
externTypeString :: External -> String
externTypeString = deBoxify . show . dynTypeRep . externDyn

-- | Remove the word 'Box' from a string.
deBoxify :: String -> String
deBoxify s | "CLSBox -> "        `isPrefixOf` s = go (drop 10 s)
           | "PrettyPrinter -> " `isPrefixOf` s = go (drop 17 s)
           | otherwise = go s
    where go xs
            | "Box" `isPrefixOf` xs = go (drop 3 xs)
          go (x:xs)                 = x : go xs
          go []                     = []

externTypeArgResString :: External -> ([String], String)
externTypeArgResString e = (map (deBoxify . show) aTys, deBoxify (show rTy))
    where (aTys, rTy) = splitExternFunType e

splitExternFunType :: External -> ([TypeRep], TypeRep)
splitExternFunType = splitFunTyArgs . dynTypeRep . externDyn

splitFunTyArgs :: TypeRep -> ([TypeRep], TypeRep)
splitFunTyArgs tr = case splitFunTyMaybe tr of
                        Nothing -> ([], tr)
                        Just (a, r) -> let (as, r') = splitFunTyArgs r
                                         in (a:as, r')

splitFunTyMaybe :: TypeRep -> Maybe (TypeRep, TypeRep)
splitFunTyMaybe (TypeRep _ tc [a,r]) | tc == funTc = Just (a,r)
splitFunTyMaybe _ = Nothing

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

-----------------------------------------------------------------

instance (Extern a, Extern b) => Extern (a -> b) where
    type Box (a -> b) = Box a -> Box b
    box f = box . f . unbox
    unbox f = unbox . f . box

-----------------------------------------------------------------

data TagBox = TagBox TagE deriving Typeable

instance Extern TagE where
    type Box TagE = TagBox
    box = TagBox
    unbox (TagBox t) = t

-----------------------------------------------------------------

data IntBox = IntBox Int deriving Typeable

instance Extern Int where
    type Box Int = IntBox
    box = IntBox
    unbox (IntBox i) = i

-----------------------------------------------------------------

data RewriteCoreBox = RewriteCoreBox (RewriteH Core) deriving Typeable

instance Extern (RewriteH Core) where
    type Box (RewriteH Core) = RewriteCoreBox
    box = RewriteCoreBox
    unbox (RewriteCoreBox r) = r

-----------------------------------------------------------------

data RewriteCoreTCBox = RewriteCoreTCBox (RewriteH CoreTC) deriving Typeable

instance Extern (RewriteH CoreTC) where
    type Box (RewriteH CoreTC) = RewriteCoreTCBox
    box = RewriteCoreTCBox
    unbox (RewriteCoreTCBox r) = r

-----------------------------------------------------------------

data BiRewriteCoreBox = BiRewriteCoreBox (BiRewriteH Core) deriving Typeable

instance Extern (BiRewriteH Core) where
    type Box (BiRewriteH Core) = BiRewriteCoreBox
    box = BiRewriteCoreBox
    unbox (BiRewriteCoreBox b) = b

-----------------------------------------------------------------

data TransformCoreTCStringBox = TransformCoreTCStringBox (TransformH CoreTC String) deriving Typeable

instance Extern (TransformH CoreTC String) where
    type Box (TransformH CoreTC String) = TransformCoreTCStringBox
    box = TransformCoreTCStringBox
    unbox (TransformCoreTCStringBox t) = t

-----------------------------------------------------------------

data TransformCoreStringBox = TransformCoreStringBox (TransformH Core String) deriving Typeable

instance Extern (TransformH Core String) where
    type Box (TransformH Core String) = TransformCoreStringBox
    box = TransformCoreStringBox
    unbox (TransformCoreStringBox t) = t

-----------------------------------------------------------------

data TransformCoreTCCheckBox = TransformCoreTCCheckBox (TransformH CoreTC ()) deriving Typeable

instance Extern (TransformH CoreTC ()) where
    type Box (TransformH CoreTC ()) = TransformCoreTCCheckBox
    box = TransformCoreTCCheckBox
    unbox (TransformCoreTCCheckBox t) = t

-----------------------------------------------------------------

data TransformCoreCheckBox = TransformCoreCheckBox (TransformH Core ()) deriving Typeable

instance Extern (TransformH Core ()) where
    type Box (TransformH Core ()) = TransformCoreCheckBox
    box = TransformCoreCheckBox
    unbox (TransformCoreCheckBox t) = t

-----------------------------------------------------------------

-- TODO: We now have CrumbBoc, PathBox and TransformCorePathBox.
--       Ints are interpreted as a TransformCorePathBox.
--       This all needs cleaning up.

data CrumbBox = CrumbBox Crumb deriving Typeable

instance Extern Crumb where
    type Box Crumb = CrumbBox
    box = CrumbBox
    unbox (CrumbBox cr) = cr

-----------------------------------------------------------------

data PathBox = PathBox LocalPathH deriving Typeable

instance Extern LocalPathH where
    type Box LocalPathH = PathBox
    box = PathBox
    unbox (PathBox p) = p

-----------------------------------------------------------------

data TransformCorePathBox = TransformCorePathBox (TransformH Core LocalPathH) deriving Typeable

instance Extern (TransformH Core LocalPathH) where
    type Box (TransformH Core LocalPathH) = TransformCorePathBox
    box = TransformCorePathBox
    unbox (TransformCorePathBox t) = t

-----------------------------------------------------------------

data TransformCoreTCPathBox = TransformCoreTCPathBox (TransformH CoreTC LocalPathH) deriving Typeable

instance Extern (TransformH CoreTC LocalPathH) where
    type Box (TransformH CoreTC LocalPathH) = TransformCoreTCPathBox
    box = TransformCoreTCPathBox
    unbox (TransformCoreTCPathBox t) = t

-----------------------------------------------------------------

newtype CoreString = CoreString { unCoreString :: String } deriving Typeable

instance Extern CoreString where
    type Box CoreString = CoreString
    box = id
    unbox = id

-----------------------------------------------------------------

data StringBox = StringBox String deriving Typeable

instance Extern String where
    type Box String = StringBox
    box = StringBox
    unbox (StringBox s) = s

-----------------------------------------------------------------

data StringListBox = StringListBox [String] deriving Typeable

instance Extern [String] where
    type Box [String] = StringListBox
    box = StringListBox
    unbox (StringListBox l) = l

-----------------------------------------------------------------

data IntListBox = IntListBox [Int] deriving Typeable

instance Extern [Int] where
    type Box [Int] = IntListBox
    box = IntListBox
    unbox (IntListBox l) = l

-----------------------------------------------------------------

data RewriteCoreListBox = RewriteCoreListBox [RewriteH Core] deriving Typeable

instance Extern [RewriteH Core] where
    type Box [RewriteH Core] = RewriteCoreListBox
    box = RewriteCoreListBox
    unbox (RewriteCoreListBox l) = l

-----------------------------------------------------------------

instance Extern LemmaName where
    type Box LemmaName = LemmaName
    box = id
    unbox = id

-----------------------------------------------------------------

data RewriteQCBox = RewriteQCBox (RewriteH QC) deriving Typeable

instance Extern (RewriteH QC) where
    type Box (RewriteH QC) = RewriteQCBox
    box = RewriteQCBox
    unbox (RewriteQCBox r) = r

-----------------------------------------------------------------

data TransformQCStringBox = TransformQCStringBox (TransformH QC String) deriving Typeable

instance Extern (TransformH QC String) where
    type Box (TransformH QC String) = TransformQCStringBox
    box = TransformQCStringBox
    unbox (TransformQCStringBox t) = t

-----------------------------------------------------------------

data TransformQCUnitBox = TransformQCUnitBox (TransformH QC ()) deriving Typeable

instance Extern (TransformH QC ()) where
    type Box (TransformH QC ()) = TransformQCUnitBox
    box = TransformQCUnitBox
    unbox (TransformQCUnitBox t) = t

-----------------------------------------------------------------
