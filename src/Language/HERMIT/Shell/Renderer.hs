{-# LANGUAGE FlexibleInstances, FlexibleContexts, ScopedTypeVariables, GADTs, TypeFamilies, DeriveDataTypeable #-}

module Language.HERMIT.Shell.Renderer where

import Data.List (isPrefixOf)
import Data.Monoid

import Language.HERMIT.Kure
import Language.HERMIT.PrettyPrinter.Common

import Language.HERMIT.Shell.Types

import System.Console.ANSI
import System.IO


showRenderers :: QueryFun
showRenderers = Message $ "set-renderer " ++ show (map fst finalRenders)

changeRenderer :: String -> ShellEffect
changeRenderer renderer = CLSModify $ \ st ->
        case lookup renderer finalRenders of
          Nothing -> return st          -- TODO: should fail with message
          Just r  -> return $ st { cl_render = r }

-------------------------------------------------------------------------------

newtype UnicodeTerminal = UnicodeTerminal (Handle -> Maybe PathH -> IO ())

instance RenderSpecial UnicodeTerminal where
        renderSpecial sym = UnicodeTerminal $ \ h _ -> hPutStr h [ch]
                where (Unicode ch) = renderSpecial sym

instance Monoid UnicodeTerminal where
        mempty = UnicodeTerminal $ \ _ _ -> return ()
        mappend (UnicodeTerminal f1) (UnicodeTerminal f2) = UnicodeTerminal $ \ h p -> f1 h p >> f2 h p

finalRenders :: [(String,Handle -> PrettyOptions -> DocH -> IO ())]
finalRenders =
        [ ("unicode-terminal", unicodeConsole)
        ] ++ coreRenders

unicodeConsole :: Handle -> PrettyOptions -> DocH -> IO ()
unicodeConsole h opts doc = do
    let (UnicodeTerminal prty) = renderCode opts doc
    prty h (po_focus opts)

doSGR :: [SGR] -> UnicodeTerminal
doSGR cmds = UnicodeTerminal $ \ h _ -> hSetSGR h cmds

undoSGRWith :: [SGR] -> [Attr] -> UnicodeTerminal
undoSGRWith cmds stk = doSGR cmds `mappend` rDoHighlight Nothing stk

setHighlight :: PathH -> Handle -> Maybe PathH -> IO ()
setHighlight _ _ Nothing   = return ()
setHighlight p h (Just fp) = hSetSGR h (if fp `isPrefixOf` p then [ SetUnderlining SingleUnderline ] else [ Reset ])

instance RenderCode UnicodeTerminal where
        rPutStr txt  = UnicodeTerminal $ \ h _ -> hPutStr h txt

        -- TODO: if we want an inplace CLI... rStart = UnicodeTerminal $ \ h _ -> hClearScreen h >> hSetCursorPosition h 0 0
        rEnd = UnicodeTerminal $ \ h _ -> hSetSGR h [ Reset ] >> hPutStrLn h ""

        -- anything that doesn't just change the foreground color needs to end itself cleanly
        rDoHighlight (Just (Color KeywordColor)) stk = undoSGRWith [SetConsoleIntensity NormalIntensity] stk
        rDoHighlight (Just (Color WarningColor)) stk = undoSGRWith [SetSwapForegroundBackground False] stk
        rDoHighlight _ [] = doSGR [ Reset ]
        rDoHighlight _ (Color col:_) =
            doSGR $ case col of
                        KeywordColor  -> [ SetConsoleIntensity BoldIntensity
                                         , SetColor Foreground Dull Blue
                                         ]
                        SyntaxColor   -> [ SetColor Foreground Dull Red ]
                        IdColor       -> [] -- equivalent to Reset
                        CoercionColor -> [ SetColor Foreground Dull Yellow ]
                        TypeColor     -> [ SetColor Foreground Dull Green ]
                        LitColor      -> [ SetColor Foreground Dull Cyan ]
                        WarningColor  -> [ SetSwapForegroundBackground True, SetColor Foreground Vivid Yellow ]
-- TODO: enable        rDoHighlight _ (PathAttr p:_) = UnicodeTerminal $ setHighlight $ snocPathToPath p
        rDoHighlight o (_:rest) = rDoHighlight o rest

