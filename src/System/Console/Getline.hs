{-# LANGUAGE ScopedTypeVariables #-}
module System.Console.Getline where

-- The Prelude version of catch has been deprecated.
import Prelude hiding (catch)
import Control.Exception (catch, SomeException)
import Data.Char
import System.IO
import System.Console.ANSI

getEditor :: IO (String -> IO (Maybe String))
getEditor = do
        setTitle "HERMIT"

        let readCh xs = do
                    c <- getChar
                    optPrint c xs

            optPrint '\n' xs = do
                     putChar '\n'
                     hFlush stdout
                     return (reverse xs)
            optPrint '\EOT' [] = do
                     putChar '\n'
                     hFlush stdout
                     return "\EOT"
            optPrint '\DEL' [] = bell []
            optPrint '\DEL' xs = do
                     cursorBackward 1
                     putStr " "
                     cursorBackward 1
                     hFlush stdout
                     readCh (tail xs)
            optPrint '\ESC' xs = escPrint xs
            optPrint c xs = do
                    if (isPrint c) then do
                        putChar c
                        hFlush stdout
                        readCh (c : xs)
                      else bell xs

            bell xs = do
                        putChar '\BEL'
                        hFlush stdout
                        readCh xs

            escPrint xs = do
                    c <- getChar
                    escPrint' c xs

            escPrint' '[' xs = do
                    c <- getChar
                    escPrintBracket c xs
            escPrint' o xs = optPrint o xs

            escPrintBracket c []
                        | c `elem` "ABCD"
                        = do
                     putChar '\n'
                     hFlush stdout
                     return ("esc-" ++ [c])
            escPrintBracket c xs
                        | otherwise
                        = bell xs

        let myGetLine :: IO String
            myGetLine = do
                  hSetBuffering stdin NoBuffering
                  hSetEcho stdin False
                  readCh []

        let gets prompt = do
                  setSGR [ SetConsoleIntensity BoldIntensity
                         , SetColor Foreground Dull Red
                         ]
                  putStr prompt
                  setSGR [ SetConsoleIntensity NormalIntensity
                         , SetColor Foreground Dull Black
                         ]
                  hFlush stdout
                  str <- myGetLine `catch` (\ (_ :: SomeException) -> return "\EOT")
                  return $ case str of
                               "\EOT" -> Nothing
                               _      -> Just str
        return $ gets

