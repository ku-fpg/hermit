{-# LANGUAGE FlexibleInstances, ScopedTypeVariables, GADTs, KindSignatures, TypeFamilies, DeriveDataTypeable #-}

module Language.HERMIT.Shell.Command where

import GhcPlugins hiding (L, Direction)

import Data.Char
import Data.Dynamic
import Control.Applicative
import Control.Arrow
import Data.List (intercalate)
import Data.Default (def)
import Control.Exception.Base hiding (catch)

import Language.HERMIT.HermitExpr
import Language.HERMIT.External
import Language.HERMIT.Interp
import Language.HERMIT.HermitKure
import Language.HERMIT.HermitEnv
import Language.HERMIT.Kernel
import Language.HERMIT.PrettyPrinter
import Language.HERMIT.Interp
import Language.HERMIT.Dictionary

import qualified Data.Map as M
import qualified Text.PrettyPrint.MarkedHughesPJ as PP
import System.Console.ANSI

import Language.KURE
import Data.Dynamic


data ShellCommand :: * where
   Status        ::                             ShellCommand
   Message       :: String                   -> ShellCommand
   PushFocus     :: LensH Core Core          -> ShellCommand
--   PopFocus      ::                             ShellCommand
   SuperPopFocus ::                             ShellCommand
   SetPretty     :: String                   -> ShellCommand
   ShellState    :: (CommandLineState -> IO CommandLineState) -> ShellCommand
   KernelCommand :: KernelCommand            -> ShellCommand
   Direction     :: Direction                -> ShellCommand

data Direction = L | R | U | D
        deriving Show

data ShellCommandBox = ShellCommandBox ShellCommand deriving Typeable

instance Extern ShellCommand where
    type Box ShellCommand = ShellCommandBox
    box i = ShellCommandBox i
    unbox (ShellCommandBox i) = i

interpShellCommand :: [Interp ShellCommand]
interpShellCommand =
                [ Interp $ \ (ShellCommandBox cmd)       -> cmd
                , Interp $ \ (LensCoreCoreBox l)         -> PushFocus l
                , Interp $ \ (IntBox i)                  -> PushFocus $ childL i
                , Interp $ \ (StringBox str)             -> Message str
                ]


shell_externals :: [External]
shell_externals = map (.+ Shell) $
   [
     external "exit"            Exit
       [ "exits HERMIT" ]
   , external "status"          Status
       [ "redisplays current state" ]
   , external "left"            (Direction L)
       [ "move to the next child"]
   , external "right"           (Direction R)
       [ "move to the previous child"]
   , external "up"              (Direction U)
       [ "move to the parent"]
   , external "down"            (Direction D)
       [ "move to the first child"]
   , external "esc-D"            (Direction L)
       [ "move to the next child"]
   , external "esc-C"           (Direction R)
       [ "move to the previous child"]
   , external "esc-A"              (Direction U)
       [ "move to the parent"]
   , external "esc-B"            (Direction D)
       [ "move to the first child"]
   , external "root"            SuperPopFocus   -- call this top
       [ "move to root of tree" ]
   , external "setpp"           SetPretty
       [ "set the pretty printer"
       , "use 'setpp ls' to list available pretty printers" ]
   , external "set-renderer"    changeRenderer
       [ "set the output renderer mode"]
   , external "set-renderer"    showRenderers
       [ "set the output renderer mode"]
   ]

showRenderers :: ShellCommand
showRenderers = Message $ "set-renderer " ++ show (M.keys finalRenders)

changeRenderer :: String -> ShellCommand
changeRenderer renderer = ShellState $ \ st ->
        case M.lookup renderer finalRenders of
          Nothing -> return st          -- should fail with message
          Just r  -> return $ st { cl_render = r }

----------------------------------------------------------------------------------

data CommandLineState = CommandLineState
        { cl_lens        :: LensH Core Core  -- ^ stack of lenses
        , cl_pretty      :: String           -- ^ which pretty printer to use
        , cl_pretty_opts :: PrettyOptions -- ^ The options for the pretty printer
        , cl_cursor      :: AST              -- ^ the current AST
        , cl_render      :: DocH -> IO ()   -- ^ the way of outputing to the screen
        }

finalRenders :: M.Map String (DocH -> IO ())
finalRenders = M.fromList
        [ ("unicode-console", unicodeConsole)
        , ("latex", \ doc -> do
                        let (LaTeXVerbatim pretty) = renderCode doc
                        putStrLn pretty)
        ]

unicodeConsole :: DocH -> IO ()
unicodeConsole doc = do
    let (UnicodeTerminal pretty) = renderCode doc
    pretty

commandLine :: IO (Maybe String) -> ModGuts -> CoreM ModGuts
commandLine gets modGuts = do
  liftIO $ print (length (mg_rules modGuts))
  let dict = dictionary shell_externals modGuts
  commandLine2 dict gets modGuts

commandLine2 :: M.Map String [Dynamic] -> IO (Maybe String) -> ModGuts -> CoreM ModGuts
commandLine2 dict gets = hermitKernel $ \ kernel ast -> do

  let quit = quitK kernel

  let query :: AST -> TranslateH Core a -> IO a
      query = queryK kernel

  let catch :: IO a -> (String -> IO a) -> IO a
      catch = catchJust (\ (err :: IOException) -> return (show err))

  let pretty :: CommandLineState -> PrettyH Core
      pretty st = case M.lookup (cl_pretty st) pp_dictionary of
                   Just pp -> pp (cl_pretty_opts st)
                   Nothing -> pure (PP.text $ "<<no pretty printer for " ++ cl_pretty st ++ ">>")

  let showFocus :: CommandLineState -> IO Bool
      showFocus st = (do
        doc <- query (cl_cursor st) (focusT (cl_lens st) (pretty st))
        cl_render st doc
        return True) `catch` \ msg -> do
                        putStrLn $ "Error thrown: " ++ msg
                        return False

  let loop :: CommandLineState -> IO ()
      loop st = do
          print (cl_pretty st,cl_cursor st)

          maybeLine <- gets
          case maybeLine of
            Nothing            -> kernelAct st Exit
            Just ('-':'-':msg) -> loop st
            Just line          ->
                if all isSpace line
                then loop st
                else case parseExprH line of
                       Left  msg  -> putStrLn ("parse failure: " ++ msg) >> loop st
                       Right expr ->
                           case interpExprH
                                        dict
                                        (interpShellCommand
                                           ++  map (fmap KernelCommand) interpKernelCommand)
                                        expr of
                            Left msg  -> putStrLn msg >> loop st
                            Right cmd -> act st cmd

      showFocusLoop :: CommandLineState -> IO ()
      showFocusLoop st = whenM (showFocus st) (loop st) -- TODO: not sure about this

      -- TODO: fix to ring bell if stuck
      showNewLens :: CommandLineState -> LensH Core Core -> IO ()
      showNewLens st new_lens = condM (query (cl_cursor st) (testM new_lens))
                                      (showFocusLoop $ st {cl_lens = new_lens})
                                      (showFocusLoop st) -- bell (still print for now)

      act :: CommandLineState -> ShellCommand -> IO ()
      act st (ShellState f) = do
              st' <- f st
              showFocusLoop st'

      act st Status = do
--              True <- showFocus st
              print "starting"
              ContextPath doc <- query (cl_cursor st) (focusT (cl_lens st) pathT)
              print (reverse doc)
              loop st
      act st (PushFocus ls) = do
              let new_lens = cl_lens st `composeL` ls
              -- below is a common ending
              showNewLens st new_lens

      act st (Direction dir) = do
              ContextPath c_path      <- query (cl_cursor st) (focusT (cl_lens st) pathT)
              child_count <- query (cl_cursor st) (focusT (cl_lens st) (arr numChildren))
              print (c_path,child_count,dir)
              let new_lens = case (dir, c_path) of
                       (U, _ : rest)              -> pathL $ reverse rest
                       (D, _)                     -> pathL $ reverse (0 : c_path)
                       (R, kid : rest)            -> pathL $ reverse ((kid + 1) : rest)
                       (L, kid : rest)  | kid > 0 -> pathL $ reverse ((kid - 1) : rest)
                       _               -> cl_lens st
              -- something changed, to print
              showNewLens st new_lens

      act st SuperPopFocus = showFocusLoop $ st {cl_lens = idL} -- something changed, to print

      act st (Message msg) = putStrLn msg >> loop st

      act st (SetPretty pp) = do
              st' <- maybe (do putStrLn $ "List of Pretty Printers: " ++ intercalate ", " (M.keys pp_dictionary)
                               return st)
                           (const $ return $ st { cl_pretty = pp })
                           (M.lookup pp pp_dictionary)
              loop st'

      act st (KernelCommand cmd) = kernelAct st cmd

      kernelAct st Exit   = quit (cl_cursor st)

      kernelAct st (Query q) = do

              -- something changed, to print
              (query (cl_cursor st) (focusT (cl_lens st) q) >>= print)
                `catch` \ msg -> putStrLn $ "Error thrown: " ++ msg
              -- same state
              loop st

      kernelAct st (Apply rr) = do
              -- something changed (you've applied)
              st2 <- (do ast' <- applyK kernel (cl_cursor st) (focusR (cl_lens st) rr)
                         let st' = st { cl_cursor = ast' }
                         showFocus st'
                         return st') `catch` \  msg -> do
                                        putStrLn $ "Error thrown: " ++ msg
                                        return st
              loop st2

  -- recurse using the command line, starting with showing the first focus
  showFocusLoop $ CommandLineState idL "clean" def ast unicodeConsole

  -- we're done
  quitK kernel ast
  return ()

newtype UnicodeTerminal = UnicodeTerminal (IO ())

terminal :: IO () -> UnicodeTerminal -> UnicodeTerminal
terminal m (UnicodeTerminal r) = UnicodeTerminal (m >> r)

instance RenderCode UnicodeTerminal where
        rPutStr (SpecialFont:_) txt = terminal $ do
                putStr [ code | Just (Unicode code) <- map renderSpecialFont txt ]
        rPutStr _              txt  = terminal $ do
                putStr txt

        rDoHighlight _ [] = terminal $ do
                setSGR [Reset]
        rDoHighlight _ (Color col:_) = terminal $ do
                setSGR [ Reset ]
                setSGR $ case col of
                        KeywordColor -> [ SetConsoleIntensity BoldIntensity
                                        , SetColor Foreground Dull Blue
                                        ]
                        SyntaxColor  -> [ SetColor Foreground Dull Red ]
                        VarColor     -> []   -- as is
                        TypeColor    -> [ SetColor Foreground Dull Green ]
                        LitColor     -> [ SetColor Foreground Dull Cyan ]
        rDoHighlight o (_:rest) = rDoHighlight o rest
        rEnd = UnicodeTerminal $ putStrLn ""


newtype LaTeXVerbatim = LaTeXVerbatim String

latexVerbatim :: String -> LaTeXVerbatim -> LaTeXVerbatim
latexVerbatim str (LaTeXVerbatim v) = LaTeXVerbatim (str ++ v)

instance RenderCode LaTeXVerbatim where
        rStart = latexVerbatim "\\begin{Verbatim}[commandchars=\\\\\\{\\}]\n"   -- be careful with escapes here

        rPutStr (SpecialFont:_) txt = latexVerbatim $
                concat [ code | Just (LaTeX code) <- map renderSpecialFont txt ]
        rPutStr _              txt  = latexVerbatim txt

        rDoHighlight False _ = latexVerbatim "}"
        rDoHighlight _ [] = latexVerbatim $ "{"
        rDoHighlight _ (Color col:_) = latexVerbatim $ "{" ++ case col of
                        KeywordColor -> "\\bf\\color{blue}"
                        SyntaxColor  -> "\\color{red}"
                        VarColor     -> ""
                        TypeColor    -> "\\color{green}"
                        LitColor     -> "\\color{cyan}"
        rDoHighlight o (_:rest) = rDoHighlight o rest
        rEnd = LaTeXVerbatim "\n\\end{Verbatim}"


