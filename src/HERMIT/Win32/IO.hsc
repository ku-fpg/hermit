-- | Adapted from circular-ruin's StackOverflow answer at <http://stackoverflow.com/a/10779150>
{-# LANGUAGE ForeignFunctionInterface, CPP, NoImplicitPrelude #-}
module HERMIT.Win32.IO (
    HERMIT.Win32.IO.putChar
  , HERMIT.Win32.IO.putStr
  , HERMIT.Win32.IO.putStrLn
  , HERMIT.Win32.IO.print
  , ePutChar
  , ePutStr
  , ePutStrLn
  , ePrint
  , HERMIT.Win32.IO.hPutChar
  , HERMIT.Win32.IO.hPutStr
  , HERMIT.Win32.IO.hPutStrLn
  , HERMIT.Win32.IO.hPrint
  , trace
  , traceIO
  ) where

#include <windows.h>

import Control.Concurrent.MVar
import Control.Exception (bracket)

import Data.Char (ord)
import Data.Typeable

import Foreign
import Foreign.C.Types

import GHC.IO.FD (FD(..)) -- A wrapper around an Int32
import GHC.IO.Handle.Types (Handle(..), Handle__(..))

import Prelude hiding (putStr, putStrLn) --(IO, Read, Show, String)

import qualified System.IO (hPutChar, hPutStr, hPutStrLn)
import System.IO hiding (putStr, putStrLn, hPutChar, hPutStr, hPutStrLn)
import System.IO.Unsafe (unsafePerformIO)
import System.Win32.Types (BOOL, HANDLE, DWORD, LPDWORD, LPWSTR, LPVOID)

-- | <http://msdn.microsoft.com/en-us/library/ms683231(VS.85).aspx>
--   HANDLE WINAPI GetStdHandle(DWORD nStdHandle);
--   returns INVALID_HANDLE_VALUE, NULL, or a valid handle
foreign import ccall unsafe "GetStdHandle"
    win32GetStdHandle :: DWORD -> IO HANDLE

sTD_OUTPUT_HANDLE, sTD_ERROR_HANDLE :: DWORD
sTD_OUTPUT_HANDLE = (#const STD_OUTPUT_HANDLE)  -- all DWORD arithmetic is performed modulo 2^n
sTD_ERROR_HANDLE  = (#const STD_ERROR_HANDLE)

-- | <http://msdn.microsoft.com/en-us/library/aa364960(VS.85).aspx>
--   DWORD WINAPI GetFileType(HANDLE hFile);
foreign import ccall unsafe "GetFileType"
    win32GetFileType :: HANDLE -> IO DWORD

fILE_TYPE_CHAR, fILE_TYPE_REMOTE :: DWORD
fILE_TYPE_CHAR   = (#const FILE_TYPE_CHAR)
fILE_TYPE_REMOTE = (#const FILE_TYPE_REMOTE)

-- | <http://msdn.microsoft.com/en-us/library/ms683167(VS.85).aspx>
--   BOOL WINAPI GetConsoleMode(HANDLE hConsole, LPDWORD lpMode);
foreign import ccall unsafe "GetConsoleMode"
    win32GetConsoleMode :: HANDLE -> LPDWORD -> IO BOOL

iNVALID_HANDLE_VALUE :: HANDLE
iNVALID_HANDLE_VALUE = intPtrToPtr $ -1

isAConsole :: HANDLE -> IO Bool
isAConsole handle
  = if (handle == iNVALID_HANDLE_VALUE) then return False
      else do ft <- win32GetFileType handle
              if ((ft .&. complement fILE_TYPE_REMOTE) /= fILE_TYPE_CHAR) then return False
                else do ptr <- malloc
                        cm  <- win32GetConsoleMode handle ptr
                        free ptr
                        return cm

-- | BOOL WINAPI WriteConsoleW(HANDLE hOutput, LPWSTR lpBuffer, DWORD nChars,
--                             LPDWORD lpCharsWritten, LPVOID lpReserved); -}
foreign import ccall unsafe "WriteConsoleW" win32WriteConsoleW
  :: HANDLE -> LPWSTR -> DWORD -> LPDWORD -> LPVOID -> IO BOOL

data ConsoleInfo = ConsoleInfo Int (Ptr CWchar) (Ptr DWORD) HANDLE

writeConsole :: ConsoleInfo -> String -> IO ()
writeConsole (ConsoleInfo bufsize buf written handle) string
  = let fillbuf :: Int -> String -> IO ()
        fillbuf i [] = emptybuf buf i []
        fillbuf i remain@(first:rest)
          | i + 1 < bufsize && ordf <= 0xffff = do pokeElemOff buf i asWord
                                                   fillbuf (i+1) rest
          | i + 1 < bufsize && ordf >  0xffff = do pokeElemOff buf i word1
                                                   pokeElemOff buf (i+1) word2
                                                   fillbuf (i+2) rest
          | otherwise                         = emptybuf buf i remain
          where ordf   = ord first
                asWord = fromInteger (toInteger ordf) :: CWchar
                sub    = ordf - 0x10000
                word1' = ((shiftR sub 10) .&. 0x3ff) + 0xD800
                word2' = (sub .&. 0x3FF)             + 0xDC00
                word1  = fromInteger . toInteger $ word1'
                word2  = fromInteger . toInteger $ word2'

        emptybuf :: (Ptr CWchar) -> Int -> String -> IO ()
        emptybuf _ 0 []     = return ()
        emptybuf _ 0 remain = fillbuf 0 remain
        emptybuf ptr nLeft remain
          = do let nLeft'    = fromInteger . toInteger $ nLeft
               ret          <- win32WriteConsoleW handle ptr nLeft' written nullPtr
               nWritten     <- peek written
               let nWritten' = fromInteger . toInteger $ nWritten
               if ret && (nWritten > 0)
                  then emptybuf (ptr `plusPtr` (nWritten' * szWChar)) (nLeft - nWritten') remain
                  else fail "WriteConsoleW failed.\n"

    in  fillbuf 0 string

szWChar :: Int
szWChar = sizeOf (0 :: CWchar)

makeConsoleInfo :: DWORD -> Handle -> IO (Either ConsoleInfo Handle)
makeConsoleInfo nStdHandle fallback = do
    handle <- win32GetStdHandle nStdHandle
    handleToConsoleInfo handle fallback

handleToConsoleInfo :: HANDLE -> Handle -> IO (Either ConsoleInfo Handle)
handleToConsoleInfo handle fallback = do
    isConsole <- isAConsole handle
    let bufsize = 10000
    if not isConsole then return $ Right fallback
        else do buf <- mallocBytes (szWChar * bufsize)
                written <- malloc
                return . Left $ ConsoleInfo bufsize buf written handle

{-# NOINLINE stdoutConsoleInfo #-}
stdoutConsoleInfo :: Either ConsoleInfo Handle
stdoutConsoleInfo = unsafePerformIO $ makeConsoleInfo sTD_OUTPUT_HANDLE stdout

{-# NOINLINE stderrConsoleInfo #-}
stderrConsoleInfo :: Either ConsoleInfo Handle
stderrConsoleInfo = unsafePerformIO $ makeConsoleInfo sTD_ERROR_HANDLE stderr

conPutChar :: ConsoleInfo -> Char -> IO ()
conPutChar ci = writeConsole ci . replicate 1

conPutStr :: ConsoleInfo -> String -> IO ()
conPutStr = writeConsole

conPutStrLn :: ConsoleInfo -> String -> IO ()
conPutStrLn ci = writeConsole ci . (++ "\n")

putChar :: Char -> IO ()
putChar = (either conPutChar System.IO.hPutChar) stdoutConsoleInfo

putStr :: String -> IO ()
putStr = (either conPutStr System.IO.hPutStr) stdoutConsoleInfo

putStrLn :: String -> IO ()
putStrLn = (either conPutStrLn System.IO.hPutStrLn) stdoutConsoleInfo

print :: Show a => a -> IO ()
print = putStrLn . show

ePutChar :: Char -> IO ()
ePutChar = (either conPutChar System.IO.hPutChar) stderrConsoleInfo

ePutStr :: String -> IO ()
ePutStr = (either conPutStr System.IO.hPutStr) stderrConsoleInfo

ePutStrLn :: String -> IO ()
ePutStrLn = (either conPutStrLn System.IO.hPutStrLn) stderrConsoleInfo

ePrint :: Show a => a -> IO ()
ePrint = ePutStrLn . show

hPutChar :: Handle -> Char -> IO ()
hPutChar haskHandle c = withHandleToHANDLE haskHandle $ \ winHandle -> do
    eitherHandle <- handleToConsoleInfo winHandle haskHandle
    either conPutChar System.IO.hPutChar eitherHandle c

hPutStr :: Handle -> String -> IO ()
hPutStr haskHandle str = withHandleToHANDLE haskHandle $ \ winHandle -> do
    eitherHandle <- handleToConsoleInfo winHandle haskHandle
    either conPutStr System.IO.hPutStr eitherHandle str

hPutStrLn :: Handle -> String -> IO ()
hPutStrLn haskHandle str = withHandleToHANDLE haskHandle $ \ winHandle -> do
    eitherHandle <- handleToConsoleInfo winHandle haskHandle
    either conPutStrLn System.IO.hPutStrLn eitherHandle str

hPrint :: Show a => Handle -> a -> IO ()
hPrint = (. show) . hPutStrLn

trace :: String -> a -> a
trace string expr = unsafePerformIO $ do
    traceIO string
    return expr

traceIO :: String -> IO ()
traceIO = ePutStrLn

-------------------------------------------------------------------------------
-- All code that follows is taken from ansi-terminal by batterseapower, which
-- is licensed under BSD3

-- This essential function comes from the C runtime system. It is certainly provided by msvcrt, and also seems to be provided by the mingw C library - hurrah!
foreign import ccall unsafe "_get_osfhandle"
    cget_osfhandle :: CInt -> IO HANDLE

-- | This bit is all highly dubious. The problem is that we want to output ANSI to arbitrary Handles rather than forcing
-- people to use stdout. However, the Windows ANSI emulator needs a Windows HANDLE to work it's magic, so we need to be able
-- to extract one of those from the Haskell Handle.
--
-- This code accomplishes this, albeit at the cost of only being compatible with GHC.
withHandleToHANDLE :: Handle -> (HANDLE -> IO a) -> IO a
withHandleToHANDLE haskell_handle action =
    -- Create a stable pointer to the Handle. This prevents the garbage collector
    -- getting to it while we are doing horrible manipulations with it, and hence
    -- stops it being finalized (and closed).
    withStablePtr haskell_handle $ const $ do
        -- Grab the write handle variable from the Handle
        let write_handle_mvar = case haskell_handle of
                FileHandle _ handle_mvar -> handle_mvar
                DuplexHandle _ _ handle_mvar -> handle_mvar -- This is "write" MVar, we could also take the "read" one

        Just fd <- fmap (\(Handle__ { haDevice = dev }) -> fmap fdFD (cast dev)) $ readMVar write_handle_mvar

        -- Finally, turn that (C-land) FD into a HANDLE using msvcrt
        windows_handle <- cget_osfhandle fd

        -- Do what the user originally wanted
        action windows_handle

withStablePtr :: a -> (StablePtr a -> IO b) -> IO b
withStablePtr value = bracket (newStablePtr value) freeStablePtr
