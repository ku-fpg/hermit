{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}

module HERMIT.Plugin.Renderer where

import Control.Arrow
import Control.Monad.State

import Data.List (isInfixOf, isPrefixOf, isSuffixOf)
import Data.Semigroup (Semigroup(..))

import HERMIT.Dictionary (traceR)
import HERMIT.Kure
import HERMIT.Plugin.Types
import HERMIT.PrettyPrinter.Common

import System.Console.ANSI
import System.IO
import System.IO.CodePage (withCP65001)
import System.IO.Temp
import System.Process

import HERMIT.Exception

changeRenderer :: String -> PluginM ()
changeRenderer renderer =
    case lookup renderer shellRenderers of
        Nothing -> fail "bad renderer option."
        Just r  -> modify $ \ st -> st { ps_render = r }

shellRenderers :: [(String,Handle -> PrettyOptions -> Either String DocH -> IO ())]
shellRenderers = [ ("unicode-terminal", unicodeConsole) ]
              ++ [ (nm, \ h opts -> either (hPutStr h) (hPutStr h . fn opts)) | (nm,fn) <- coreRenders ]

-------------------------------------------------------------------------------

newtype UnicodeTerminal = UnicodeTerminal (Handle -> Maybe PathH -> IO ())

instance RenderSpecial UnicodeTerminal where
        renderSpecial sym = UnicodeTerminal $ \ h _ -> hPutStr h [ch]
                where (Unicode ch) = renderSpecial sym

instance Monoid UnicodeTerminal where
        mempty = UnicodeTerminal $ \ _ _ -> return ()
        mappend = (<>)

instance Semigroup UnicodeTerminal where
        UnicodeTerminal f1 <> UnicodeTerminal f2 = UnicodeTerminal $ \ h p -> f1 h p >> f2 h p

unicodeConsole :: Handle -> PrettyOptions -> Either String DocH -> IO ()
unicodeConsole h opts = withCP65001 . go
  where
    go :: Either String DocH -> IO ()
    go (Left str)  = hPutStr h str
    go (Right doc) = let UnicodeTerminal r = renderCode opts doc
                      in r h $ po_focus opts

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

----------------------------------------------------------------------------------------------

-- TODO: this should be in PrettyPrinter.Common, but is here because it relies on
--       unicodeConsole to get nice colored diffs. We can either switch to straight unicode
--       renderer and give up on color, or come up with a clever solution.
diffDocH :: (MonadCatch m, MonadIO m) => PrettyPrinter -> DocH -> DocH -> m String
diffDocH pp doc1 doc2 =
    liftAndCatchIO $
        withSystemTempFile "A.dump" $ \ fp1 h1 ->
            withSystemTempFile "B.dump" $ \ fp2 h2 ->
                withSystemTempFile "AB.diff" $ \ fp3 h3 -> do
                    let opts = pOptions pp
                    unicodeConsole h1 opts (Right doc1)
                    hFlush h1
                    unicodeConsole h2 opts (Right doc2)
                    hFlush h2
                    let cmd = unwords ["diff", "-b", "-U 5", fp1, fp2]
                        p = (shell cmd) { std_out = UseHandle h3 , std_err = UseHandle h3 }
                    (_,_,_,h) <- createProcess p
                    _ <- waitForProcess h
                    res <- readFile fp3
                    -- strip out some of the diff lines
                    return $ unlines [ l | l <- lines res, not (fp1 `isInfixOf` l || fp2 `isInfixOf` l)
                                                         , not ("@@" `isPrefixOf` l && "@@" `isSuffixOf` l) ]

-- TODO: again this should be elsewhere, but is here because diffDocH is here.
diffR :: Injection a LCoreTC => PrettyPrinter -> String -> RewriteH a -> RewriteH a
diffR pp msg rr = do
    let ppT = extractT $ liftPrettyH (pOptions pp) (pLCoreTC pp)
        runDiff b a = do
            doc1 <- return b >>> ppT
            doc2 <- return a >>> ppT
            r <- diffDocH pp doc1 doc2
            return a >>> traceR (msg ++ " diff:\n" ++ r)

    -- Be careful to only run the rr once, in case it has side effects.
    (e,r) <- idR &&& attemptM rr
    either (fail . (show :: HException -> String)) (runDiff e) r


