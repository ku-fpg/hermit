{-# LANGUAGE FlexibleInstances, ScopedTypeVariables, GADTs, KindSignatures, TypeFamilies, DeriveDataTypeable #-}

module Language.HERMIT.Shell.Command where

import Language.HERMIT.External
import Language.HERMIT.Interp
import Language.HERMIT.HermitKure
import Language.HERMIT.Kernel

import Language.KURE
import Data.Dynamic


data ShellCommand :: * where
   Status        ::                             ShellCommand
   Message       :: String                   -> ShellCommand
   PushFocus     :: LensH Core Core          -> ShellCommand
   PopFocus      ::                             ShellCommand
   SuperPopFocus ::                             ShellCommand
   SetPretty     :: String                   -> ShellCommand
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
   , external "pop"             PopFocus
       [ "pops one lens" ]
   , external "."               PopFocus
       [ "pops one lens" ]
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
   , external "root"            SuperPopFocus
       [ "move to root of tree" ]
   , external "superpop"        SuperPopFocus
       [ "pops all lenses" ]
   , external "setpp"           SetPretty
       [ "set the pretty printer"
       , "use 'setpp ls' to list available pretty printers" ]
   ]
