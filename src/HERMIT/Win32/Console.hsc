{-# LANGUAGE ForeignFunctionInterface #-}
-- | Taken from <https://github.com/batterseapower/ansi-terminal/blob/master/System/Console/ANSI/Windows/Foreign.hs> in the ansi-terminal package by batterseapower, licensed under BSD3
module HERMIT.Win32.Console (getConsoleWindowSize) where

import Control.Applicative

import Foreign.C.Types
import Foreign.Marshal
import Foreign.Ptr
import Foreign.Storable

import System.Win32.Types

#include <windows.h>
#let alignment t = "%lu", (unsigned long)offsetof(struct {char x__; t (y__); }, y__)

type SHORT = CShort

getConsoleWindowSize :: IO (Maybe (Int, Int))
getConsoleWindowSize = do
    hStdout <- getStdHandle sTD_OUTPUT_HANDLE
    csbiInfo <- getConsoleScreenBufferInfo hStdout
    return $ fmap coords csbiInfo
        where coords :: CONSOLE_SCREEN_BUFFER_INFO -> (Int, Int)
              coords info = case csbi_maximum_window_size info of
                                 (COORD x y) -> (fromIntegral x, fromIntegral y)

sTD_OUTPUT_HANDLE :: DWORD
sTD_OUTPUT_HANDLE = #{const STD_OUTPUT_HANDLE}

foreign import stdcall unsafe "windows.h GetStdHandle"
    getStdHandle :: DWORD -> IO HANDLE
foreign import stdcall unsafe "windows.h GetConsoleScreenBufferInfo"
    cGetConsoleScreenBufferInfo :: HANDLE -> Ptr CONSOLE_SCREEN_BUFFER_INFO -> IO BOOL

getConsoleScreenBufferInfo :: HANDLE -> IO (Maybe CONSOLE_SCREEN_BUFFER_INFO)
getConsoleScreenBufferInfo handle = alloca $ \ptr_console_screen_buffer_info -> do
    ret <- cGetConsoleScreenBufferInfo handle ptr_console_screen_buffer_info
    if ret then peek ptr_console_screen_buffer_info >>= return . Just
           else return Nothing

data CONSOLE_SCREEN_BUFFER_INFO = CONSOLE_SCREEN_BUFFER_INFO {
        _csbi_size :: COORD,
        _csbi_cursor_position :: COORD,
        _csbi_attributes :: WORD,
        _csbi_window :: SMALL_RECT,
        csbi_maximum_window_size :: COORD
    }

instance Storable CONSOLE_SCREEN_BUFFER_INFO where
    sizeOf _ = #{size CONSOLE_SCREEN_BUFFER_INFO}
    alignment _ = #{alignment CONSOLE_SCREEN_BUFFER_INFO}
    peek ptr = CONSOLE_SCREEN_BUFFER_INFO                        <$>
        #{peek CONSOLE_SCREEN_BUFFER_INFO, dwSize} ptr           <*>
        #{peek CONSOLE_SCREEN_BUFFER_INFO, dwCursorPosition} ptr <*>
        #{peek CONSOLE_SCREEN_BUFFER_INFO, wAttributes} ptr      <*>
        #{peek CONSOLE_SCREEN_BUFFER_INFO, srWindow} ptr         <*>
        #{peek CONSOLE_SCREEN_BUFFER_INFO, dwMaximumWindowSize} ptr
    poke ptr (CONSOLE_SCREEN_BUFFER_INFO size cursor_position attributes window maximum_window_size) = do
        #{poke CONSOLE_SCREEN_BUFFER_INFO, dwSize} ptr size
        #{poke CONSOLE_SCREEN_BUFFER_INFO, dwCursorPosition} ptr cursor_position
        #{poke CONSOLE_SCREEN_BUFFER_INFO, wAttributes} ptr attributes
        #{poke CONSOLE_SCREEN_BUFFER_INFO, srWindow} ptr window
        #{poke CONSOLE_SCREEN_BUFFER_INFO, dwMaximumWindowSize} ptr maximum_window_size

data COORD = COORD SHORT SHORT

instance Storable COORD where
    sizeOf _ = #{size COORD}
    alignment _ = #{alignment COORD}
    peek ptr =
        COORD <$> #{peek COORD, X} ptr
              <*> #{peek COORD, Y} ptr
    poke ptr (COORD x y) = do
        #{poke COORD, X} ptr x
        #{poke COORD, Y} ptr y

data SMALL_RECT = SMALL_RECT SHORT SHORT SHORT SHORT

instance Storable SMALL_RECT where
    sizeOf _ = #{size SMALL_RECT}
    alignment _ = #{alignment SMALL_RECT}
    peek ptr =
        SMALL_RECT <$> #{peek SMALL_RECT, Left} ptr
                   <*> #{peek SMALL_RECT, Top} ptr
                   <*> #{peek SMALL_RECT, Right} ptr
                   <*> #{peek SMALL_RECT, Bottom} ptr
    poke ptr (SMALL_RECT l t r b) = do
        #{poke SMALL_RECT, Left} ptr l
        #{poke SMALL_RECT, Top} ptr t
        #{poke SMALL_RECT, Right} ptr r
        #{poke SMALL_RECT, Bottom} ptr b