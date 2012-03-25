{-# LANGUAGE RankNTypes, ScopedTypeVariables, FlexibleInstances, KindSignatures, GADTs #-}

-- A Hermitage is a place of quiet reflection.

module Language.HERMIT.Hermitage where

import GhcPlugins

import System.Environment
import System.Console.Editline

import Language.HERMIT.HermitEnv
import Language.HERMIT.HermitMonad
import Language.HERMIT.Types

-- abstact outside this module
data Hermitage c a = Hermitage
        { ageModGuts :: ModGuts
        , ageFocus   :: Focus c a
        }
--        { close :: IO () }

-- Create a new Hermitage, does not return until the interaction
-- is completed. It is thread safe (any thread can call a 'Hermitage' function),
-- but not after the callback has terminated and returned.
new :: (Hermitage () ModGuts -> IO (Hermitage () ModGuts)) -> ModGuts -> CoreM ModGuts
new k modGuts = do
        liftIO $ k (Hermitage modGuts InitialFocus)
        return modGuts

-- Some of these do not need to be in IO,
-- but there are plans for async-access, memoization, etc,
-- so we'll stick them in the monad right now.

-- | What are the current module guts?
getModGuts :: Hermitage c a -> IO ModGuts
getModGuts age = return (ageModGuts age)


-- | 'getForeground' gets the current 'blob' under consideraton.
getForeground :: Hermitage c a -> IO a
getForeground age = return $ undefined -- ageExtract age (ageModGuts age)

{-

-- | getBackground gets the background of the Hermitage,
-- getBackground


-}

data Focus :: * -> * -> * where
    InitialFocus ::                          Focus () ModGuts
    AppendFocus  :: Focus a b -> Zoom b c -> Focus (a,b) c

-- Invarient, The project gets the same thing as the rewrite transformes
data Zoom a b = Zoom
        { rewriteD :: Rewrite b -> Rewrite a
        , projectD :: Translate a b
        }

{-
data Focus :: * -> * -> * where
    FocusOnBinding :: Focus c (Bind Id) -- new focus is binding [group] containing a specific Id.
    FocusOnRhs     :: Id -> Focus c (Expr Id) -- new focus is left-hand-side of the binding of a specific Id.
    FocusOnExpr    :: (Expr Id -> Bool) -> Focus c (Expr Id) -- new focus using a expression predicated.
-}

focusHermitage :: Zoom a x
               -> Hermitage c a
               -> Either HermitMessage (Hermitage (c,a) x)
focusHermitage zoom age = Right $ Hermitage
        { ageModGuts = ageModGuts age
        , ageFocus   = ageFocus age `AppendFocus` zoom
        }

-- focusHermitage (FocusOnBinding) (Hermitage {}) = undefined

unfocusHermitage :: Hermitage (c,a) x -> Hermitage c a
unfocusHermitage age = Hermitage
        { ageModGuts = ageModGuts age
        , ageFocus   = case ageFocus age of
                          AppendFocus old zoom_ -> old
                          -- initial case not possible due to typing
        }

applyRewrite :: Rewrite a -> Hermitage c a -> IO (Hermitage c a)
applyRewrite = undefined

------------------------------------------------------------------

focusOnBinding :: (Term a) => Zoom a (Bind Id)
focusOnBinding = error "focusOnBinding"

------------------------------------------------------------------

data HermitMessage
        = UnableToFocusMessage
        deriving (Show)

------------------------------------------------------------------

commandLine :: Hermitage () ModGuts -> IO (Hermitage () ModGuts)
commandLine h = do
    prog <- getProgName
    el <- elInit prog
    setEditor el Emacs
    let loop :: forall c a . (Term a, Show2 a) => Int -> Hermitage c a -> IO (Hermitage c a)
        loop n h = do
         setPrompt el (return $ show n ++ "> ")
         maybeLine <- elGets el
         case maybeLine of
             Nothing ->
                do print "ctrl-D"
                   return h
--             return h -- ctrl-D
             Just line -> do
                 let line' = init line -- remove trailing '\n'
                 putStrLn $ "User input: " ++ show line'
                 case words line' of
                    ["?"] -> do
                        a <- getForeground h
                        putStrLn "Foreground: "
                        putStrLn (show2 a)
                        loop n h
                    ["focus"] -> do
                        case focusHermitage (focusOnBinding) h of
                           Left msg -> do
                             print msg
                             loop n h
                           Right h1 -> do
                             loop (succ n) h1
                             let h2 = unfocusHermitage h1
                             loop n h2
                    other -> do
                        putStrLn $ "do not understand " ++ show other
                        loop n h

--         interp


    loop 0 h

-- Later, this will have depth, and other pretty print options.
class Show2 a where
        show2 :: a -> String

instance Show2 ModGuts where
        show2 _ = "ModGuts"

instance Show2 (Expr Id) where
        show2 _ = "ModGuts"

instance Show2 (Bind Id) where
        show2 _ = "ModGuts"

t = undefined :: Translate ModGuts Int
t2 = undefined :: Translate Int Bool
t3 = undefined :: Translate Bool Float
