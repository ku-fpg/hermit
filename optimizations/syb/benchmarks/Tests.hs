{-# LANGUAGE ScopedTypeVariables #-}

module Tests (Library(..), TestName(..), Test(..), Datatype(..), tests) where

import System.FilePath ((</>))

--------------------------------------------------------------------------------
-- Datatypes for representing libraries, tests, and datatypes tested on
--------------------------------------------------------------------------------

data Library = Hand          -- Handwritten code
             | HandPar       -- Handwritten code, parallelised
             | SYB           -- syb-0.1
             | MultiRec      -- multirec-0.4
             | MultiRecInline-- multirec-0.4 with INLINE pragmas
             | Instant       -- instant-generics-0.1
             | InstantInline -- instant-generics-0.1 with INLINE pragmas
             | Deriving      -- generic-deriving-0.4 with INLINE pragmas
                deriving (Eq, Ord, Show)

data TestName = Eq
              | Map
              | Read
              | Show
              | Update      -- Traversals
              | Arbitrary   -- QuickCheck's (1.2)
              | Enum
              | Decode
              | RmWeights   -- from GPBench's RmWeights
              | SelectInt   -- from GPBench's FoldTree
              | RenumberInt -- everywhereM
                 deriving (Eq, Ord, Show)

data Test = Test { lib :: Library,
                   testName :: TestName,
                   datatype :: Datatype,
                   ghcFlags :: String
                 } deriving (Eq, Ord, Show)

test :: Library -> TestName -> Datatype -> Test
test l t d = Test l t d ""

htest :: Library -> TestName -> Datatype -> String -> Test
htest l t d f = Test l t d hermitFlags
    where hermitFlags = unwords ["-dcore-lint"             -- HERMIT sanity check
                                ,"-fsimple-list-literals"  -- HERMIT
                                ,"-fexpose-all-unfoldings" -- optimization diverges without
                                ,"-fplugin=HERMIT.Optimization.SYB"
                                ,modPrefix ++ f            -- function targetted by optimization
                                ]
          modPrefix = "-fplugin-opt=HERMIT.Optimization.SYB:" ++ show l ++ "." ++ show t ++ ".Main:"

data Datatype = Tree    -- Labelled binary trees
              | Logic   -- Logic expressions
              | Nat     -- Peano naturals
              | List    -- Haskell lists
              | WTree   -- Weighted Tree from GPBench
                deriving (Eq, Ord, Show)


--------------------------------------------------------------------------------
-- Tests
--------------------------------------------------------------------------------

allTests, handTests, sybTests, multirecTests, instantTests, instantInlineTests,
  multirecInlineTests, derivingTests, tests :: [Test]
handTests = [ test Hand Eq     Tree
            , test Hand Map    Tree
            , test Hand Read   Tree
            , test Hand Show   Tree
--            , test Hand Update Tree
            , test Hand Enum   Tree
            , test Hand Enum   Nat
            , test Hand Decode Tree
            , test Hand Eq     Logic
            , test Hand Read   Logic
            , test Hand Show   Logic
            , test Hand Update Logic
            , test Hand Enum   Logic
            , test Hand Decode Logic
            , test Hand RmWeights WTree
            , test Hand SelectInt WTree
            , test Hand RenumberInt Tree
            , test Hand RenumberInt Logic]

handParTests = [ test HandPar Eq     Tree
               , test HandPar Map    Tree
               --, test HandPar Read   Tree
               , test HandPar Show   Tree
               , test HandPar Update Tree
               , test HandPar Enum   Tree
               --, test HandPar Decode Tree
               , test HandPar Eq     Logic
               --, test HandPar Read   Logic
               , test HandPar Show   Logic
               , test HandPar Update Logic
               , test HandPar Enum   Logic
               --, test HandPar Decode Logic
               ]

sybTests = [ test SYB Eq     Tree
           , test SYB Map    Tree
           , test SYB Read   Tree
           , test SYB Show   Tree
--           , test SYB Update Tree
           , test SYB Enum   Tree
           , test SYB Eq     Logic
           , test SYB Read   Logic
           , test SYB Show   Logic
           , test SYB Update Logic
           , test SYB Enum   Logic
           , test SYB RmWeights WTree
           , test SYB SelectInt WTree
           , test SYB RenumberInt Tree
           , test SYB RenumberInt Logic
           ]

hermitSybTests =
    [ htest SYB Map         Tree "incTree"
--    , htest SYB Update      Tree ""
    , htest SYB Update      Logic "updateString"
    , htest SYB RmWeights   WTree "mainWTree"
    , htest SYB SelectInt   WTree "mainWTree"
    , htest SYB RenumberInt Tree  "mainTree"
    , htest SYB RenumberInt Logic "mainLogic"
    ]

multirecTests = [ test MultiRec Eq     Tree
                , test MultiRec Show   Tree
                , test MultiRec Read   Tree
                , test MultiRec Update Tree
                , test MultiRec Eq     Logic
                , test MultiRec Show   Logic
                -- , test MultiRec Read   Logic
                , test MultiRec Update Logic]

multirecInlineTests = [ test MultiRecInline Eq     Tree
                      -- , test MultiRecInline Show   Tree
                      -- , test MultiRecInline Read   Tree
                      , test MultiRecInline Update Tree
                      , test MultiRecInline Eq     Logic
                      -- , test MultiRecInline Show   Logic
                      -- , test MultiRecInline Read   Logic
                      -- , test MultiRecInline Update Logic
                      ]

instantTests = [ test Instant Eq     Tree
               , test Instant Show   Tree
               , test Instant Update Tree
               , test Instant Enum   Tree
               , test Instant Enum   Nat
               , test Instant Decode Tree
               , test Instant Eq     Logic
               , test Instant Show   Logic
               , test Instant Update Logic
               , test Instant Enum   Logic
               , test Instant Decode Logic]

instantInlineTests = [ test InstantInline Eq     Tree
                     , test InstantInline Show   Tree
                     , test InstantInline Update Tree
                     , test InstantInline Enum   Tree
                     , test InstantInline Enum   Nat
                     , test InstantInline Decode Tree
                     , test InstantInline Eq     Logic
                     , test InstantInline Show   Logic
                     , test InstantInline Update Logic
                     , test InstantInline Enum   Logic
                     , test InstantInline Decode Logic]

derivingTests = [ test Deriving Eq     Tree
                , test Deriving Map    Tree
                , test Deriving Show   Tree
                -- , test Deriving Update Tree
                , test Deriving Enum   Tree
                -- , test Deriving Decode Tree
                , test Deriving Eq     Logic
                , test Deriving Show   Logic
                -- , test Deriving Update Logic
                , test Deriving Enum   Logic
                -- , test Deriving Decode Logic
                , test Deriving Enum   Nat
                ]


allTests =    handTests ++ handParTests
           ++ sybTests ++ hermitSybTests
           ++ multirecTests ++ multirecInlineTests
           ++ instantTests  ++ instantInlineTests
           ++ derivingTests

tests = [ t | t <- allTests
        , lib t `elem` [Hand, SYB]
        , testName t `elem` [RenumberInt, Map, Update, RmWeights, SelectInt]
        ]
